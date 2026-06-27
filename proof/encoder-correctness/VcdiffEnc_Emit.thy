theory VcdiffEnc_Emit
  imports
    VcdiffEnc_Wire
    VcdiffEnc_Cache_Opcode
begin

context vcdiff_enc_global_addresses begin

lemma emit_inst_spec_RAdd_small_sections:
  fixes sz :: "32 word"
  assumes sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
      and bs_len: "length bs = unat sz"
  shows "enc_data (emit_inst_spec src_len (RAdd bs) st) = enc_data st @ bs"
    and "enc_inst (emit_inst_spec src_len (RAdd bs) st) =
         enc_inst st @ [ucast (1 + sz)]"
    and "enc_addr (emit_inst_spec src_len (RAdd bs) st) = enc_addr st"
    and "enc_cache (emit_inst_spec src_len (RAdd bs) st) = enc_cache st"
    and "enc_flushed (emit_inst_spec src_len (RAdd bs) st) =
         enc_flushed st + length bs"
proof -
  have sz_nat_ge: "1 \<le> unat sz"
    using sz_ge by (simp add: word_le_nat_alt)
  have sz_nat_le: "unat sz \<le> 17"
    using sz_le by (simp add: word_le_nat_alt)
  have unat_suc: "unat (1 + sz :: 32 word) = 1 + unat sz"
    using sz_nat_le by (simp add: unat_word_ariths)
  have op_byte: "(word_of_nat (1 + unat sz) :: byte) = ucast (1 + sz)"
    using byte_of_unat_ucast32[of "1 + sz"] unat_suc by simp
  have add_opcode:
    "find_single_add_opcode (length bs) = (1 + unat sz, False)"
    using sz_nat_ge sz_nat_le bs_len
    by (simp add: find_single_add_opcode_def)
  show "enc_data (emit_inst_spec src_len (RAdd bs) st) = enc_data st @ bs"
    using add_opcode
    by (simp add: emit_inst_spec_def Let_def)
  show "enc_inst (emit_inst_spec src_len (RAdd bs) st) =
         enc_inst st @ [ucast (1 + sz)]"
    using add_opcode op_byte
    by (simp add: emit_inst_spec_def Let_def)
  show "enc_addr (emit_inst_spec src_len (RAdd bs) st) = enc_addr st"
    using add_opcode
    by (simp add: emit_inst_spec_def Let_def)
  show "enc_cache (emit_inst_spec src_len (RAdd bs) st) = enc_cache st"
    using add_opcode
    by (simp add: emit_inst_spec_def Let_def)
  show "enc_flushed (emit_inst_spec src_len (RAdd bs) st) =
         enc_flushed st + length bs"
    using add_opcode
    by (simp add: emit_inst_spec_def Let_def)
qed

lemma emit_inst_spec_RAdd_large_sections:
  fixes sz :: "32 word"
  assumes sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and bs_len: "length bs = unat sz"
      and size: "varint_size' sz s = Some n"
  shows "enc_data (emit_inst_spec src_len (RAdd bs) st) = enc_data st @ bs"
    and "enc_inst (emit_inst_spec src_len (RAdd bs) st) =
         enc_inst st @ [1] @ varint_bytes32 sz n"
    and "enc_addr (emit_inst_spec src_len (RAdd bs) st) = enc_addr st"
    and "enc_cache (emit_inst_spec src_len (RAdd bs) st) = enc_cache st"
    and "enc_flushed (emit_inst_spec src_len (RAdd bs) st) =
         enc_flushed st + length bs"
proof -
  have add_opcode:
    "find_single_add_opcode (length bs) = (1, True)"
    using sz_large bs_len
    by (auto simp: find_single_add_opcode_def word_le_nat_alt)
  show "enc_data (emit_inst_spec src_len (RAdd bs) st) = enc_data st @ bs"
    using add_opcode
    by (simp add: emit_inst_spec_def Let_def)
  show "enc_inst (emit_inst_spec src_len (RAdd bs) st) =
         enc_inst st @ [1] @ varint_bytes32 sz n"
    using add_opcode bs_len varint_bytes32_eq_varint_encode[OF size]
    by (simp add: emit_inst_spec_def Let_def)
  show "enc_addr (emit_inst_spec src_len (RAdd bs) st) = enc_addr st"
    using add_opcode
    by (simp add: emit_inst_spec_def Let_def)
  show "enc_cache (emit_inst_spec src_len (RAdd bs) st) = enc_cache st"
    using add_opcode
    by (simp add: emit_inst_spec_def Let_def)
  show "enc_flushed (emit_inst_spec src_len (RAdd bs) st) =
         enc_flushed st + length bs"
    using add_opcode
    by (simp add: emit_inst_spec_def Let_def)
qed

lemma emit_inst_spec_RRun_sections:
  fixes sz :: "32 word"
  assumes size: "varint_size' sz s = Some n"
  shows "enc_data (emit_inst_spec src_len (RRun fill (unat sz)) st) =
         enc_data st @ [fill]"
    and "enc_inst (emit_inst_spec src_len (RRun fill (unat sz)) st) =
         enc_inst st @ [0] @ varint_bytes32 sz n"
    and "enc_addr (emit_inst_spec src_len (RRun fill (unat sz)) st) =
         enc_addr st"
    and "enc_cache (emit_inst_spec src_len (RRun fill (unat sz)) st) =
         enc_cache st"
    and "enc_flushed (emit_inst_spec src_len (RRun fill (unat sz)) st) =
         enc_flushed st + unat sz"
  using varint_bytes32_eq_varint_encode[OF size]
  by (simp_all add: emit_inst_spec_def Let_def find_single_run_opcode_def)

lemma emit_inst_spec_RAdd_sections_general:
  shows "enc_data (emit_inst_spec src_len (RAdd bs) st) = enc_data st @ bs"
    and "enc_inst (emit_inst_spec src_len (RAdd bs) st) =
         enc_inst st @ add_inst_bytes (length bs)"
    and "enc_addr (emit_inst_spec src_len (RAdd bs) st) = enc_addr st"
    and "enc_cache (emit_inst_spec src_len (RAdd bs) st) = enc_cache st"
    and "enc_flushed (emit_inst_spec src_len (RAdd bs) st) =
         enc_flushed st + length bs"
  by (simp_all add: emit_inst_spec_def add_inst_bytes_def Let_def split: prod.splits)

lemma emit_inst_spec_RRun_sections_general:
  shows "enc_data (emit_inst_spec src_len (RRun fill n) st) =
         enc_data st @ [fill]"
    and "enc_inst (emit_inst_spec src_len (RRun fill n) st) =
         enc_inst st @ run_inst_bytes n"
    and "enc_addr (emit_inst_spec src_len (RRun fill n) st) = enc_addr st"
    and "enc_cache (emit_inst_spec src_len (RRun fill n) st) = enc_cache st"
    and "enc_flushed (emit_inst_spec src_len (RRun fill n) st) =
         enc_flushed st + n"
  by (simp_all add: emit_inst_spec_def run_inst_bytes_def Let_def
                    find_single_run_opcode_def split: prod.splits)

lemma emit_copy_spec_small_sections:
  fixes copy_addr copy_len :: "32 word"
  assumes sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
      and addr_choice:
        "encode_address (enc_cache st) (unat copy_addr)
           (src_len + enc_flushed st) =
         (unat (mode_t_C.mode_C m), addr_bytes,
          cache_update (enc_cache st) (unat copy_addr))"
  shows "enc_data
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_data st"
    and "enc_inst
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_inst st @
           [ucast (op_t_C.op_C
             (single_copy_opcode' copy_len (mode_t_C.mode_C m)))]"
    and "enc_addr
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_addr st @ addr_bytes"
    and "enc_cache
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         cache_update (enc_cache st) (unat copy_addr)"
    and "enc_flushed
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_flushed st + unat copy_len"
proof -
  let ?op = "single_copy_opcode' copy_len (mode_t_C.mode_C m)"
  have needs: "op_t_C.needs_size_C ?op = 0"
    using single_copy_opcode'_small[OF sz_ge sz_le] by auto
  have find:
    "find_single_copy_opcode (unat copy_len) (unat (mode_t_C.mode_C m)) =
     (unat (op_t_C.op_C ?op), False)"
    using single_copy_opcode'_find_single_copy_opcode[OF mode_le, of copy_len]
          needs
    by simp
  show "enc_data
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_data st"
    using addr_choice find
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  show "enc_inst
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_inst st @
           [ucast (op_t_C.op_C
             (single_copy_opcode' copy_len (mode_t_C.mode_C m)))]"
    using addr_choice find byte_of_unat_ucast32[of "op_t_C.op_C ?op"]
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  show "enc_addr
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_addr st @ addr_bytes"
    using addr_choice find
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  show "enc_cache
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         cache_update (enc_cache st) (unat copy_addr)"
    using addr_choice find
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  show "enc_flushed
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_flushed st + unat copy_len"
    using addr_choice find
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
qed

lemma emit_copy_spec_large_sections:
  fixes copy_addr copy_len :: "32 word"
  assumes sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
      and size: "varint_size' copy_len s = Some sn"
      and addr_choice:
        "encode_address (enc_cache st) (unat copy_addr)
           (src_len + enc_flushed st) =
         (unat (mode_t_C.mode_C m), addr_bytes,
          cache_update (enc_cache st) (unat copy_addr))"
  shows "enc_data
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_data st"
    and "enc_inst
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_inst st @
           [ucast (op_t_C.op_C
             (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
           varint_bytes32 copy_len sn"
    and "enc_addr
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_addr st @ addr_bytes"
    and "enc_cache
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         cache_update (enc_cache st) (unat copy_addr)"
    and "enc_flushed
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_flushed st + unat copy_len"
proof -
  let ?op = "single_copy_opcode' copy_len (mode_t_C.mode_C m)"
  have needs: "op_t_C.needs_size_C ?op = 1"
    using single_copy_opcode'_large[OF sz_large] by auto
  have find:
    "find_single_copy_opcode (unat copy_len) (unat (mode_t_C.mode_C m)) =
     (unat (op_t_C.op_C ?op), True)"
    using single_copy_opcode'_find_single_copy_opcode[OF mode_le, of copy_len]
          needs
    by simp
  have bytes_eq: "varint_encode (unat copy_len) = varint_bytes32 copy_len sn"
    using varint_bytes32_eq_varint_encode[OF size] by simp
  show "enc_data
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_data st"
    using addr_choice find bytes_eq
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  show "enc_inst
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_inst st @
           [ucast (op_t_C.op_C
             (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
           varint_bytes32 copy_len sn"
    using addr_choice find bytes_eq byte_of_unat_ucast32[of "op_t_C.op_C ?op"]
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  show "enc_addr
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_addr st @ addr_bytes"
    using addr_choice find bytes_eq
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  show "enc_cache
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         cache_update (enc_cache st) (unat copy_addr)"
    using addr_choice find bytes_eq
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  show "enc_flushed
           (emit_copy_spec src_len (unat copy_addr) (unat copy_len) st) =
         enc_flushed st + unat copy_len"
    using addr_choice find bytes_eq
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
qed

lemma try_emit_add_copy_spec_pending_empty_none:
  assumes pending_empty: "enc_pending st = []"
  shows "try_emit_add_copy_spec src_len copy_addr copy_len st = None"
  using pending_empty
  by (simp add: try_emit_add_copy_spec_def)

lemma try_emit_add_copy_spec_early_none:
  assumes pending_len: "length (enc_pending st) = unat pend_len"
      and early:
        "pend_len < (1 :: 32 word) \<or>
         (4 :: 32 word) < pend_len \<or>
         copy_len < (4 :: 32 word)"
  shows "try_emit_add_copy_spec src_len copy_addr (unat copy_len) st = None"
  using pending_len early
  by (auto simp: try_emit_add_copy_spec_def min_match_def
                 word_less_nat_alt)

lemma try_emit_add_copy_spec_mode_gt5_copy_ne4_none:
  assumes addr_choice:
        "encode_address (enc_cache st) copy_addr (src_len + enc_tp st) =
         (unat (mode_t_C.mode_C m), addr_bytes, cache')"
      and mode_gt: "(5 :: 32 word) < mode_t_C.mode_C m"
      and copy_ne: "copy_len \<noteq> (4 :: 32 word)"
  shows "try_emit_add_copy_spec src_len copy_addr (unat copy_len) st = None"
proof -
  have mode_gt_nat: "5 < unat (mode_t_C.mode_C m)"
    using mode_gt by (simp add: word_less_nat_alt)
  have copy_ne_nat: "unat copy_len \<noteq> 4"
  proof
    assume eq: "unat copy_len = 4"
    have "copy_len = word_of_nat (unat copy_len)"
      by simp
    also have "... = (4 :: 32 word)"
      using eq by simp
    finally show False
      using copy_ne by simp
  qed
  show ?thesis
    using addr_choice mode_gt_nat copy_ne_nat
    by (auto simp: try_emit_add_copy_spec_def fused_copy_len_spec_def
                   min_match_def Let_def
             split: option.splits prod.splits)
qed

lemma try_emit_add_copy_spec_mode_le5_success:
  fixes pend_len copy_len mode csz op :: "32 word"
  defines "csz \<equiv> (if (6 :: 32 word) < copy_len then (6 :: 32 word) else copy_len)"
      and "op \<equiv>
        (163 + mode * 12 + (pend_len - 1) * 3 + (csz - 4) :: 32 word)"
  assumes pending_len: "length (enc_pending st) = unat pend_len"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_len"
      and mode_le: "mode \<le> (5 :: 32 word)"
      and addr_choice:
        "encode_address (enc_cache st) (unat copy_addr)
           (src_len + enc_tp st) =
         (unat mode, addr_bytes, cache_update (enc_cache st) (unat copy_addr))"
  shows "try_emit_add_copy_spec src_len (unat copy_addr) (unat copy_len) st =
    Some (st \<lparr> enc_tp := enc_tp st + unat csz
             , enc_flushed := enc_flushed st + unat pend_len + unat csz
             , enc_pending := []
             , enc_data := enc_data st @ enc_pending st
             , enc_inst := enc_inst st @ [ucast op]
             , enc_addr := enc_addr st @ addr_bytes
             , enc_cache := cache_update (enc_cache st) (unat copy_addr)
             , enc_trace := enc_trace st
                 @ [RAdd (enc_pending st), RCopy (unat copy_addr) (unat csz)]
             \<rparr>)"
proof -
  have pend_nat: "1 \<le> unat pend_len" "unat pend_len \<le> 4"
    using pend_ge pend_le by (simp_all add: word_le_nat_alt)
  have copy_nat: "4 \<le> unat copy_len"
    using copy_ge by (simp add: word_le_nat_alt)
  have mode_nat: "unat mode \<le> 5"
    using mode_le by (simp add: word_le_nat_alt)
  have csz_nat: "unat csz = min (unat copy_len) 6"
    using copy_ge unfolding csz_def
    by (auto simp: word_less_nat_alt word_le_nat_alt)
  then have csz_range: "4 \<le> unat csz" "unat csz \<le> 6"
    using copy_nat by simp_all
  have fused:
    "fused_copy_len_spec (unat mode) (unat copy_len) = Some (unat csz)"
    using mode_nat copy_nat csz_nat
    by (simp add: fused_copy_len_spec_def min_match_def)
  have find:
    "find_add_copy_opcode (unat pend_len) (unat csz) (unat mode) =
     Some (unat op)"
    using pend_ge pend_le mode_le csz_range
    unfolding op_def
    by (simp add: find_add_copy_opcode_def word_le_nat_alt
                  unat_word_ariths)
  have op_byte: "(word_of_nat (unat op) :: byte) = ucast op"
    by (rule byte_of_unat_ucast32)
  show ?thesis
    using pending_len pend_nat copy_nat addr_choice fused find op_byte
    by (simp add: try_emit_add_copy_spec_def min_match_def Let_def)
qed

lemma try_emit_add_copy_spec_mode_gt5_success:
  fixes pend_len copy_len mode op :: "32 word"
  defines "op \<equiv> (235 + (mode - 6) * 4 + (pend_len - 1) :: 32 word)"
  assumes pending_len: "length (enc_pending st) = unat pend_len"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_eq: "copy_len = (4 :: 32 word)"
      and mode_gt: "(5 :: 32 word) < mode"
      and mode_le: "mode \<le> (8 :: 32 word)"
      and addr_choice:
        "encode_address (enc_cache st) (unat copy_addr)
           (src_len + enc_tp st) =
         (unat mode, addr_bytes, cache_update (enc_cache st) (unat copy_addr))"
  shows "try_emit_add_copy_spec src_len (unat copy_addr) (unat copy_len) st =
    Some (st \<lparr> enc_tp := enc_tp st + unat copy_len
             , enc_flushed := enc_flushed st + unat pend_len + unat copy_len
             , enc_pending := []
             , enc_data := enc_data st @ enc_pending st
             , enc_inst := enc_inst st @ [ucast op]
             , enc_addr := enc_addr st @ addr_bytes
             , enc_cache := cache_update (enc_cache st) (unat copy_addr)
             , enc_trace := enc_trace st
                 @ [RAdd (enc_pending st),
                    RCopy (unat copy_addr) (unat copy_len)]
             \<rparr>)"
proof -
  have pend_nat: "1 \<le> unat pend_len" "unat pend_len \<le> 4"
    using pend_ge pend_le by (simp_all add: word_le_nat_alt)
  have mode_nat: "6 \<le> unat mode" "unat mode \<le> 8"
    using mode_gt mode_le by (simp_all add: word_less_nat_alt word_le_nat_alt)
  have copy_nat: "unat copy_len = 4"
    using copy_eq by simp
  have fused:
    "fused_copy_len_spec (unat mode) (unat copy_len) = Some (unat copy_len)"
    using mode_nat copy_nat
    by (simp add: fused_copy_len_spec_def)
  have find:
    "find_add_copy_opcode (unat pend_len) (unat copy_len) (unat mode) =
     Some (unat op)"
    using pend_ge pend_le copy_eq mode_gt mode_le
    unfolding op_def
    by (simp add: find_add_copy_opcode_def word_le_nat_alt
                  word_less_nat_alt unat_word_ariths)
  have op_byte: "(word_of_nat (unat op) :: byte) = ucast op"
    by (rule byte_of_unat_ucast32)
  show ?thesis
    using pending_len pend_nat copy_nat addr_choice fused find op_byte
    by (simp add: try_emit_add_copy_spec_def min_match_def Let_def)
qed

declare emit_inst_spec_RAdd_small_sections[enc_emit_simps]
declare emit_inst_spec_RAdd_large_sections[enc_emit_simps]
declare emit_inst_spec_RRun_sections[enc_emit_simps]
declare emit_copy_spec_small_sections[enc_emit_simps]
declare emit_copy_spec_large_sections[enc_emit_simps]
declare try_emit_add_copy_spec_pending_empty_none[enc_fused_simps]
declare try_emit_add_copy_spec_early_none[enc_fused_simps]
declare try_emit_add_copy_spec_mode_gt5_copy_ne4_none[enc_fused_simps]
declare try_emit_add_copy_spec_mode_le5_success[enc_fused_simps]
declare try_emit_add_copy_spec_mode_gt5_success[enc_fused_simps]

lemma flush_pending_spec_empty_sections:
  assumes pending_empty: "enc_pending st = []"
  shows "enc_data (flush_pending_spec src_len st) = enc_data st"
    and "enc_inst (flush_pending_spec src_len st) = enc_inst st"
    and "enc_addr (flush_pending_spec src_len st) = enc_addr st"
  using pending_empty
  by (simp_all add: flush_pending_spec_def flush_pending_insts_def
                    emit_insts_spec_def append_add_inst_def
                    close_pending_run_def pending_scan_init_def)

lemma length_dropWhile_less_Suc:
  "length (dropWhile P xs) < Suc (length xs)"
  by (induction xs) auto

function flush_pending_groups ::
  "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list" where
  "flush_pending_groups add [] = append_add_inst add []"
| "flush_pending_groups add (b # bs) =
    (let run = b # takeWhile ((=) b) bs;
         rest = dropWhile ((=) b) bs
     in if min_run \<le> length run
        then append_add_inst add [] @ [RRun b (length run)] @
             flush_pending_groups [] rest
        else flush_pending_groups (add @ run) rest)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(add, rest). length rest)")
     (auto intro: length_dropWhile_less_Suc)

lemma append_add_inst_append:
  "append_add_inst bs (out @ ys) = out @ append_add_inst bs ys"
  by (simp add: append_add_inst_def)

lemma emit_insts_spec_append[simp]:
  "emit_insts_spec src_len (xs @ ys) st =
   emit_insts_spec src_len ys (emit_insts_spec src_len xs st)"
  by (simp add: emit_insts_spec_def)

lemma emit_insts_spec_append_add_inst_empty[simp]:
  "emit_insts_spec src_len (append_add_inst add []) st =
   (if add = [] then st else emit_inst_spec src_len (RAdd add) st)"
  by (simp add: append_add_inst_def emit_insts_spec_def)

lemma close_pending_run_no_run[simp]:
  "ps_run_byte (close_pending_run s) = None"
  by (simp add: close_pending_run_def split: option.splits)

lemma close_pending_run_idem[simp]:
  "close_pending_run (close_pending_run s) = close_pending_run s"
  by (simp add: close_pending_run_def split: option.splits)

lemma takeWhile_eq_replicate:
  "takeWhile ((=) b) bs =
    replicate (length (takeWhile ((=) b) bs)) b"
  by (induction bs) auto

lemma dropWhile_hd_not:
  assumes "dropWhile P xs = y # ys"
  shows "\<not> P y"
  using assms by (induction xs) (auto split: if_splits)

lemma foldl_pending_scan_step_replicate_current:
  assumes run_byte: "ps_run_byte s = Some b"
  shows "foldl pending_scan_step s (replicate n b) =
   s\<lparr>ps_run_len := ps_run_len s + n\<rparr>"
  using run_byte
  by (induction n arbitrary: s)
     (simp_all add: pending_scan_step_def ac_simps)

lemma foldl_pending_scan_step_replicate_none:
  assumes none: "ps_run_byte s = None"
  shows "foldl pending_scan_step s (replicate n b) =
    (if n = 0 then s
     else s\<lparr>ps_run_byte := Some b, ps_run_len := n\<rparr>)"
  using none
  by (cases n)
     (simp_all add: pending_scan_step_def
                    foldl_pending_scan_step_replicate_current)

lemma pending_scan_step_close_pending_run_diff:
  assumes rb: "ps_run_byte s = Some b"
      and diff: "c \<noteq> b"
  shows "pending_scan_step s c =
    pending_scan_step (close_pending_run s) c"
  using rb diff
  by (simp add: pending_scan_step_def)

lemma close_pending_run_foldl_diff:
  assumes rb: "ps_run_byte s = Some b"
      and rest_hd: "rest = [] \<or> hd rest \<noteq> b"
  shows "close_pending_run (foldl pending_scan_step s rest) =
    close_pending_run
      (foldl pending_scan_step (close_pending_run s) rest)"
  using assms
  apply (cases rest)
   apply simp
  apply (simp add: pending_scan_step_close_pending_run_diff)
  done

lemma flush_pending_groups_scan:
  "append_add_inst
      (ps_add (close_pending_run
        (foldl pending_scan_step
          (pending_scan_init\<lparr>ps_add := add, ps_out := out\<rparr>) rest)))
      (ps_out (close_pending_run
        (foldl pending_scan_step
          (pending_scan_init\<lparr>ps_add := add, ps_out := out\<rparr>) rest))) =
    out @ flush_pending_groups add rest"
proof (induction rest arbitrary: add out rule: length_induct)
  case (1 rest)
  show ?case
  proof (cases rest)
    case Nil
    then show ?thesis
      by (simp add: pending_scan_init_def close_pending_run_def
                    append_add_inst_def)
  next
    case (Cons b bs)
    let ?tw = "takeWhile ((=) b) bs"
    let ?run = "b # ?tw"
    let ?r = "dropWhile ((=) b) bs"
    let ?n = "length ?run"
    let ?s0 = "pending_scan_init\<lparr>ps_add := add, ps_out := out\<rparr>"
    let ?srun =
      "?s0\<lparr>ps_run_byte := Some b, ps_run_len := ?n\<rparr>"
    have rest_split: "rest = ?run @ ?r"
      using Cons by simp
    have run_repl: "?run = replicate ?n b"
      using takeWhile_eq_replicate[of b bs] by simp
    have fold_run:
      "foldl pending_scan_step ?s0 ?run = ?srun"
    proof -
      let ?s1 = "?s0\<lparr>ps_run_byte := Some b, ps_run_len := 1\<rparr>"
      have tw_repl:
        "?tw = replicate (length ?tw) b"
        by (rule takeWhile_eq_replicate)
      have cur:
        "foldl pending_scan_step ?s1 (replicate (length ?tw) b) =
          ?s1\<lparr>ps_run_len := ps_run_len ?s1 + length ?tw\<rparr>"
        by (rule foldl_pending_scan_step_replicate_current) simp
      show ?thesis
        using tw_repl cur
        by (simp add: pending_scan_step_def pending_scan_init_def)
    qed
    have fold_tw:
      "foldl pending_scan_step (pending_scan_step ?s0 b) ?tw = ?srun"
      using fold_run by simp
    have bs_split: "bs = ?tw @ ?r"
      by simp
    have fold_split:
      "foldl pending_scan_step ?s0 rest =
        foldl pending_scan_step ?srun ?r"
    proof -
      have fold_tail:
        "foldl pending_scan_step (pending_scan_step ?s0 b) bs =
         foldl pending_scan_step
          (foldl pending_scan_step (pending_scan_step ?s0 b) ?tw) ?r"
        using bs_split by (metis foldl_append)
      have "foldl pending_scan_step ?s0 rest =
        foldl pending_scan_step (pending_scan_step ?s0 b) bs"
        using Cons by simp
      also have "... = foldl pending_scan_step ?srun ?r"
        using fold_tail fold_tw by simp
      finally show ?thesis .
    qed
    have r_less: "length ?r < length rest"
      using Cons length_dropWhile_less_Suc[of "((=) b)" bs] by simp
    have IH:
      "\<And>add' out'.
        append_add_inst
          (ps_add (close_pending_run
            (foldl pending_scan_step
              (pending_scan_init\<lparr>ps_add := add', ps_out := out'\<rparr>) ?r)))
          (ps_out (close_pending_run
            (foldl pending_scan_step
              (pending_scan_init\<lparr>ps_add := add', ps_out := out'\<rparr>) ?r))) =
        out' @ flush_pending_groups add' ?r"
      using "1.IH" r_less by blast
    have r_hd: "?r = [] \<or> hd ?r \<noteq> b"
    proof (cases ?r)
      case Nil
      then show ?thesis by simp
    next
      case (Cons c cs)
      then have "c \<noteq> b"
        using dropWhile_hd_not[of "((=) b)" bs c cs] by simp
      then show ?thesis
        using Cons by simp
    qed
    have close_shift:
      "close_pending_run
        (foldl pending_scan_step ?srun ?r) =
       close_pending_run
        (foldl pending_scan_step (close_pending_run ?srun) ?r)"
      apply (rule close_pending_run_foldl_diff)
       apply simp
      apply (rule r_hd)
      done
    show ?thesis
    proof (cases "min_run \<le> ?n")
      case True
      have close_run:
        "close_pending_run ?srun =
          pending_scan_init
            \<lparr>ps_add := [],
             ps_out := append_add_inst add out @ [RRun b ?n]\<rparr>"
        using True by (simp add: close_pending_run_def
                                pending_scan_init_def)
      have lhs:
        "append_add_inst
          (ps_add (close_pending_run
            (foldl pending_scan_step ?s0 rest)))
          (ps_out (close_pending_run
            (foldl pending_scan_step ?s0 rest))) =
        (append_add_inst add out @ [RRun b ?n]) @
          flush_pending_groups [] ?r"
        using fold_split close_shift close_run
              IH[where add' = "[] :: byte list"
                 and out' = "append_add_inst add out @ [RRun b ?n]"]
        by simp
      show ?thesis
        using Cons True lhs
        by (simp add: append_add_inst_def)
    next
      case False
      have close_run:
        "close_pending_run ?srun =
          pending_scan_init
            \<lparr>ps_add := add @ ?run, ps_out := out\<rparr>"
        using False run_repl
        by (simp add: close_pending_run_def pending_scan_init_def)
      have lhs:
        "append_add_inst
          (ps_add (close_pending_run
            (foldl pending_scan_step ?s0 rest)))
          (ps_out (close_pending_run
            (foldl pending_scan_step ?s0 rest))) =
        out @ flush_pending_groups (add @ ?run) ?r"
        using fold_split close_shift close_run
              IH[where add' = "add @ ?run" and out' = out]
        by simp
      show ?thesis
        using Cons False lhs by simp
    qed
  qed
qed

lemma flush_pending_groups_empty_eq_insts:
  "flush_pending_groups [] pending = flush_pending_insts pending"
  using flush_pending_groups_scan[of "[]" "[]" pending]
  by (simp add: flush_pending_insts_def pending_scan_init_def)

lemma flush_pending_spec_groups:
  "flush_pending_spec src_len st =
    (emit_insts_spec src_len
      (flush_pending_groups [] (enc_pending st)) st)
      \<lparr>enc_pending := []\<rparr>"
  using flush_pending_groups_empty_eq_insts[of "enc_pending st"]
  by (simp add: flush_pending_spec_def)

lemma flush_pending_groups_short_branch:
  assumes grp_def: "grp = b # takeWhile ((=) b) bs"
      and rest_def: "rest = dropWhile ((=) b) bs"
      and short: "length grp < min_run"
  shows "flush_pending_groups add (b # bs) =
    flush_pending_groups (add @ grp) rest"
  using assms by simp

lemma flush_pending_groups_run_branch:
  assumes grp_def: "grp = b # takeWhile ((=) b) bs"
      and rest_def: "rest = dropWhile ((=) b) bs"
      and long: "min_run \<le> length grp"
  shows "flush_pending_groups add (b # bs) =
    append_add_inst add [] @ [RRun b (length grp)] @
      flush_pending_groups [] rest"
  using assms by simp

lemma flush_pending_groups_exit:
  "flush_pending_groups add [] = append_add_inst add []"
  by simp

lemma section_decodes_emit_append_add_inst:
  assumes old:
    "section_decodes src_seg tgt_len
       (enc_data st) (enc_inst st) (enc_addr st) target (enc_cache st)"
      and len32: "length add < 2 ^ 32"
      and tgt_ok: "length target + length add \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       (enc_data (emit_insts_spec src_len (append_add_inst add []) st))
       (enc_inst (emit_insts_spec src_len (append_add_inst add []) st))
       (enc_addr (emit_insts_spec src_len (append_add_inst add []) st))
       (target @ add)
       (enc_cache (emit_insts_spec src_len (append_add_inst add []) st))"
proof (cases "add = []")
  case True
  then show ?thesis
    using old by (simp add: append_add_inst_def emit_insts_spec_def)
next
  case False
  have dec:
    "section_decodes src_seg tgt_len
       (enc_data st @ add) (enc_inst st @ add_inst_bytes (length add))
       (enc_addr st) (target @ add) (enc_cache st)"
    by (rule section_decodes_append_add[OF old len32 tgt_ok])
  show ?thesis
    using False dec
    by (simp add: append_add_inst_def emit_insts_spec_def
                  emit_inst_spec_RAdd_sections_general)
qed

lemma section_decodes_emit_run_chunk:
  assumes old:
    "section_decodes src_seg tgt_len
       (enc_data st) (enc_inst st) (enc_addr st) target (enc_cache st)"
      and n_pos: "0 < n"
      and n32: "n < 2 ^ 32"
      and tgt_ok: "length target + n \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       (enc_data (emit_insts_spec src_len [RRun b n] st))
       (enc_inst (emit_insts_spec src_len [RRun b n] st))
       (enc_addr (emit_insts_spec src_len [RRun b n] st))
       (target @ replicate n b)
       (enc_cache (emit_insts_spec src_len [RRun b n] st))"
proof -
  have dec:
    "section_decodes src_seg tgt_len
       (enc_data st @ [b]) (enc_inst st @ run_inst_bytes n)
       (enc_addr st) (target @ replicate n b) (enc_cache st)"
    by (rule section_decodes_append_run[OF old n_pos n32 tgt_ok])
  show ?thesis
    using dec
    by (simp add: emit_insts_spec_def emit_inst_spec_RRun_sections_general)
qed

lemma section_decodes_flush_pending_add_run_chunks:
  assumes old:
    "section_decodes src_seg tgt_len
       (enc_data st) (enc_inst st) (enc_addr st) target (enc_cache st)"
      and add32: "length add < 2 ^ 32"
      and run_pos: "0 < n"
      and run32: "n < 2 ^ 32"
      and tgt_ok: "length target + length add + n \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       (enc_data (emit_insts_spec src_len
          (append_add_inst add [] @ [RRun b n]) st))
       (enc_inst (emit_insts_spec src_len
          (append_add_inst add [] @ [RRun b n]) st))
       (enc_addr (emit_insts_spec src_len
          (append_add_inst add [] @ [RRun b n]) st))
       (target @ add @ replicate n b)
       (enc_cache (emit_insts_spec src_len
          (append_add_inst add [] @ [RRun b n]) st))"
proof -
  let ?st_add = "emit_insts_spec src_len (append_add_inst add []) st"
  have add_tgt_ok: "length target + length add \<le> tgt_len"
    using tgt_ok by simp
  have add_dec:
    "section_decodes src_seg tgt_len
       (enc_data ?st_add) (enc_inst ?st_add) (enc_addr ?st_add)
       (target @ add) (enc_cache ?st_add)"
    by (rule section_decodes_emit_append_add_inst[
        OF old add32 add_tgt_ok])
  have run_tgt_ok: "length (target @ add) + n \<le> tgt_len"
    using tgt_ok by simp
  have run_dec:
    "section_decodes src_seg tgt_len
       (enc_data (emit_insts_spec src_len [RRun b n] ?st_add))
       (enc_inst (emit_insts_spec src_len [RRun b n] ?st_add))
       (enc_addr (emit_insts_spec src_len [RRun b n] ?st_add))
       ((target @ add) @ replicate n b)
       (enc_cache (emit_insts_spec src_len [RRun b n] ?st_add))"
    by (rule section_decodes_emit_run_chunk[
        OF add_dec run_pos run32 run_tgt_ok])
  show ?thesis
    using run_dec by (simp add: append_assoc)
qed

lemma section_decodes_copy_append_varint_addr:
  assumes old:
    "section_decodes src_seg tgt_len data inst addr target c"
      and mode_wf: "enc_mode_arg_wf c copy_addr here m"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and n_pos: "0 < n"
      and n32: "n < 2 ^ 32"
      and tgt_ok: "length target + n \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       data (inst @ copy_inst_bytes n (unat (mode_t_C.mode_C m)))
       (addr @ varint_bytes32 (mode_t_C.arg_C m) an)
       (copy_loop src_seg target (unat copy_addr) n)
       (cache_update c (unat copy_addr))"
proof -
  have mode_le: "unat (mode_t_C.mode_C m) \<le> 8"
    by (rule enc_mode_arg_wf_mode_le8[OF mode_wf])
  have here32: "length src_seg + length target < 2 ^ 32"
    using here_eq unat_lt2p[of here] by simp
  have copy_addr32: "unat copy_addr < 2 ^ 32"
    using unat_lt2p[of copy_addr] by simp
  have wf:
    "wf_encoding c (unat copy_addr) (length src_seg + length target)
       (unat (mode_t_C.mode_C m))
       (varint_bytes32 (mode_t_C.arg_C m) an)"
    using enc_mode_arg_wf_wf_encoding_varint_bytes32[
        OF mode_wf mode_lt addr_size] here_eq
    by simp
  show ?thesis
    by (rule section_decodes_copy_append[
        OF old mode_le n_pos n32 copy_addr32 here32 addr_ok tgt_ok wf])
qed

lemma section_decodes_copy_append_byte_addr:
  assumes old:
    "section_decodes src_seg tgt_len data inst addr target c"
      and mode_wf: "enc_mode_arg_wf c copy_addr here m"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and n_pos: "0 < n"
      and n32: "n < 2 ^ 32"
      and tgt_ok: "length target + n \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       data (inst @ copy_inst_bytes n (unat (mode_t_C.mode_C m)))
       (addr @ [ucast (mode_t_C.arg_C m)])
       (copy_loop src_seg target (unat copy_addr) n)
       (cache_update c (unat copy_addr))"
proof -
  have mode_le: "unat (mode_t_C.mode_C m) \<le> 8"
    by (rule enc_mode_arg_wf_mode_le8[OF mode_wf])
  have here32: "length src_seg + length target < 2 ^ 32"
    using here_eq unat_lt2p[of here] by simp
  have copy_addr32: "unat copy_addr < 2 ^ 32"
    using unat_lt2p[of copy_addr] by simp
  have wf:
    "wf_encoding c (unat copy_addr) (length src_seg + length target)
       (unat (mode_t_C.mode_C m)) [ucast (mode_t_C.arg_C m)]"
    using enc_mode_arg_wf_wf_encoding_byte[OF mode_wf mode_ge] here_eq
    by simp
  show ?thesis
    by (rule section_decodes_copy_append[
        OF old mode_le n_pos n32 copy_addr32 here32 addr_ok tgt_ok wf])
qed

lemma section_decodes_fused_add_copy_append_varint_addr:
  assumes old:
    "section_decodes src_seg tgt_len data inst addr target c"
      and fop: "find_add_copy_opcode (length add_bs) copy_n
          (unat (mode_t_C.mode_C m)) = Some op"
      and mode_wf: "enc_mode_arg_wf c copy_addr here m"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and here_eq:
        "unat here = length src_seg + length target + length add_bs"
      and addr_ok:
        "unat copy_addr < length src_seg + length target + length add_bs"
      and tgt_ok: "length target + length add_bs + copy_n \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       (data @ add_bs) (inst @ [word_of_nat op])
       (addr @ varint_bytes32 (mode_t_C.arg_C m) an)
       (copy_loop src_seg (target @ add_bs) (unat copy_addr) copy_n)
       (cache_update c (unat copy_addr))"
proof -
  have here32:
    "length src_seg + length target + length add_bs < 2 ^ 32"
    using here_eq unat_lt2p[of here] by simp
  have copy_addr32: "unat copy_addr < 2 ^ 32"
    using unat_lt2p[of copy_addr] by simp
  have wf:
    "wf_encoding c (unat copy_addr)
       (length src_seg + length target + length add_bs)
       (unat (mode_t_C.mode_C m))
       (varint_bytes32 (mode_t_C.arg_C m) an)"
    using enc_mode_arg_wf_wf_encoding_varint_bytes32[
        OF mode_wf mode_lt addr_size] here_eq
    by simp
  show ?thesis
    by (rule section_decodes_fused_add_copy_append[
        OF old fop copy_addr32 here32 addr_ok tgt_ok wf])
qed

lemma section_decodes_fused_add_copy_append_byte_addr:
  assumes old:
    "section_decodes src_seg tgt_len data inst addr target c"
      and fop: "find_add_copy_opcode (length add_bs) copy_n
          (unat (mode_t_C.mode_C m)) = Some op"
      and mode_wf: "enc_mode_arg_wf c copy_addr here m"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and here_eq:
        "unat here = length src_seg + length target + length add_bs"
      and addr_ok:
        "unat copy_addr < length src_seg + length target + length add_bs"
      and tgt_ok: "length target + length add_bs + copy_n \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       (data @ add_bs) (inst @ [word_of_nat op])
       (addr @ [ucast (mode_t_C.arg_C m)])
       (copy_loop src_seg (target @ add_bs) (unat copy_addr) copy_n)
       (cache_update c (unat copy_addr))"
proof -
  have here32:
    "length src_seg + length target + length add_bs < 2 ^ 32"
    using here_eq unat_lt2p[of here] by simp
  have copy_addr32: "unat copy_addr < 2 ^ 32"
    using unat_lt2p[of copy_addr] by simp
  have wf:
    "wf_encoding c (unat copy_addr)
       (length src_seg + length target + length add_bs)
       (unat (mode_t_C.mode_C m)) [ucast (mode_t_C.arg_C m)]"
    using enc_mode_arg_wf_wf_encoding_byte[OF mode_wf mode_ge] here_eq
    by simp
  show ?thesis
    by (rule section_decodes_fused_add_copy_append[
        OF old fop copy_addr32 here32 addr_ok tgt_ok wf])
qed

lemma takeWhile_eq_take_maximal_from:
  assumes i_lt_j: "i < j"
      and j_le: "j \<le> length xs"
      and all_eq: "\<And>k. \<lbrakk> i \<le> k; k < j \<rbrakk> \<Longrightarrow> xs ! k = b"
      and stop: "j < length xs \<Longrightarrow> xs ! j \<noteq> b"
  shows "takeWhile ((=) b) (drop i xs) =
         take (j - i) (drop i xs)"
proof (rule takeWhile_eq_take_P_nth)
  fix k
  assume k_lt: "k < j - i" and k_drop: "k < length (drop i xs)"
  have i_le_len: "i \<le> length xs"
    using i_lt_j j_le by simp
  have ik_lt: "i + k < j"
    using i_lt_j k_lt by simp
  have eq: "xs ! (i + k) = b"
    apply (rule all_eq)
     apply simp
    apply (rule ik_lt)
    done
  show "((=) b) ((drop i xs) ! k)"
    using i_le_len eq by simp
next
  assume n_lt: "j - i < length (drop i xs)"
  have i_le_len: "i \<le> length xs"
    using i_lt_j j_le by simp
  have j_lt: "j < length xs"
    using n_lt i_lt_j j_le by simp
  have idx: "i + (j - i) = j"
    using i_lt_j by simp
  show "\<not> ((=) b) ((drop i xs) ! (j - i))"
    using stop[OF j_lt] i_le_len idx by simp
qed

lemma dropWhile_eq_drop_maximal_from:
  assumes i_lt_j: "i < j"
      and j_le: "j \<le> length xs"
      and all_eq: "\<And>k. \<lbrakk> i \<le> k; k < j \<rbrakk> \<Longrightarrow> xs ! k = b"
      and stop: "j < length xs \<Longrightarrow> xs ! j \<noteq> b"
  shows "dropWhile ((=) b) (drop i xs) =
         drop (j - i) (drop i xs)"
proof -
  have tw:
    "takeWhile ((=) b) (drop i xs) =
     take (j - i) (drop i xs)"
    by (rule takeWhile_eq_take_maximal_from[
        OF i_lt_j j_le all_eq stop])
  have len_le: "j - i \<le> length (drop i xs)"
    using i_lt_j j_le by simp
  show ?thesis
    using tw len_le by (simp add: dropWhile_eq_drop)
qed

lemma flush_pending_groups_run_from_maximal:
  assumes i_lt_j: "i < j"
      and j_le: "j \<le> length xs"
      and min_len: "min_run \<le> j - i"
      and all_eq: "\<And>k. \<lbrakk> i \<le> k; k < j \<rbrakk> \<Longrightarrow> xs ! k = b"
      and stop: "j < length xs \<Longrightarrow> xs ! j \<noteq> b"
  shows "flush_pending_groups add (drop i xs) =
         append_add_inst add [] @ [RRun b (j - i)] @
         flush_pending_groups [] (drop j xs)"
proof -
  have i_lt_len: "i < length xs"
    using i_lt_j j_le by simp
  have drop_i:
    "drop i xs = b # drop (Suc i) xs"
    using Cons_nth_drop_Suc[OF i_lt_len] all_eq[of i] i_lt_j by simp
  have tw:
    "takeWhile ((=) b) (drop i xs) =
     take (j - i) (drop i xs)"
    by (rule takeWhile_eq_take_maximal_from[
        OF i_lt_j j_le all_eq stop])
  have dw:
    "dropWhile ((=) b) (drop i xs) =
     drop (j - i) (drop i xs)"
    by (rule dropWhile_eq_drop_maximal_from[
        OF i_lt_j j_le all_eq stop])
  have run_len:
    "length (take (j - i) (drop i xs)) = j - i"
    using i_lt_j j_le by simp
  have rest:
    "drop (j - i) (drop i xs) = drop j xs"
    using i_lt_j by (simp add: drop_drop)
  show ?thesis
    using drop_i tw dw min_len run_len rest
    by (simp add: Cons_nth_drop_Suc i_lt_len)
qed

lemma flush_pending_groups_short_from_maximal:
  assumes i_lt_j: "i < j"
      and j_le: "j \<le> length xs"
      and short: "j - i < min_run"
      and all_eq: "\<And>k. \<lbrakk> i \<le> k; k < j \<rbrakk> \<Longrightarrow> xs ! k = b"
      and stop: "j < length xs \<Longrightarrow> xs ! j \<noteq> b"
  shows "flush_pending_groups add (drop i xs) =
         flush_pending_groups
           (add @ take (j - i) (drop i xs)) (drop j xs)"
proof -
  have i_lt_len: "i < length xs"
    using i_lt_j j_le by simp
  have drop_i:
    "drop i xs = b # drop (Suc i) xs"
    using Cons_nth_drop_Suc[OF i_lt_len] all_eq[of i] i_lt_j by simp
  have tw:
    "takeWhile ((=) b) (drop i xs) =
     take (j - i) (drop i xs)"
    by (rule takeWhile_eq_take_maximal_from[
        OF i_lt_j j_le all_eq stop])
  have dw:
    "dropWhile ((=) b) (drop i xs) =
     drop (j - i) (drop i xs)"
    by (rule dropWhile_eq_drop_maximal_from[
        OF i_lt_j j_le all_eq stop])
  have run_len:
    "length (take (j - i) (drop i xs)) = j - i"
    using i_lt_j j_le by simp
  have rest:
    "drop (j - i) (drop i xs) = drop j xs"
    using i_lt_j by (simp add: drop_drop)
  show ?thesis
    using drop_i tw dw short run_len rest
    by (simp add: Cons_nth_drop_Suc i_lt_len)
qed

lemma heap_bytes_word_zero_take_drop:
  fixes off sz len :: "32 word"
  assumes range: "unat off + unat sz \<le> unat len"
  shows "heap_bytes_word s buf off sz =
         take (unat sz) (drop (unat off) (heap_bytes_word s buf 0 len))"
proof -
  have bytes:
    "heap_bytes s buf (unat len) = heap_bytes_word s buf 0 len"
    by (simp add: heap_bytes_word_zero)
  show ?thesis
    by (rule heap_bytes_word_eq_take_drop_heap_bytes[OF bytes range])
qed

lemma heap_bytes_word_zero_take_drop_between:
  fixes i j len :: "32 word"
  assumes i_le_j: "i \<le> j"
      and j_le_len: "j \<le> len"
  shows "heap_bytes_word s buf i (j - i) =
         take (unat (j - i))
           (drop (unat i) (heap_bytes_word s buf 0 len))"
proof -
  have range: "unat i + unat (j - i) \<le> unat len"
    using i_le_j j_le_len
    by (simp add: unat_sub word_le_nat_alt)
  show ?thesis
    by (rule heap_bytes_word_zero_take_drop[OF range])
qed

lemma take_drop_append_between:
  assumes a_le_i: "a \<le> i"
      and i_le_j: "i \<le> j"
      and j_le_len: "j \<le> length xs"
  shows "take (i - a) (drop a xs) @ take (j - i) (drop i xs) =
         take (j - a) (drop a xs)"
proof (rule nth_equalityI)
  show "length (take (i - a) (drop a xs) @ take (j - i) (drop i xs)) =
        length (take (j - a) (drop a xs))"
    using assms by simp
next
  fix k
  assume k_lt:
    "k < length (take (i - a) (drop a xs) @ take (j - i) (drop i xs))"
  have k_lt_total: "k < j - a"
    using k_lt assms by simp
  show "(take (i - a) (drop a xs) @ take (j - i) (drop i xs)) ! k =
        take (j - a) (drop a xs) ! k"
  proof (cases "k < i - a")
    case True
    have a_k_lt_len: "a + k < length xs"
      using k_lt_total j_le_len a_le_i i_le_j by simp
    have k_lt_drop_a: "k < length xs - a"
      using a_k_lt_len by simp
    then show ?thesis
      using True k_lt_total a_k_lt_len k_lt_drop_a
      by (simp add: nth_append)
  next
    case False
    let ?m = "k - (i - a)"
    have m_lt: "?m < j - i"
      using False k_lt_total a_le_i i_le_j by simp
    have idx: "i + ?m = a + k"
      using False a_le_i by simp
    have i_m_lt_len: "i + ?m < length xs"
      using m_lt j_le_len i_le_j by simp
    have a_k_lt_len: "a + k < length xs"
      using idx i_m_lt_len by simp
    have k_lt_drop_a: "k < length xs - a"
      using a_k_lt_len by simp
    have m_lt_drop_i: "?m < length xs - i"
      using i_m_lt_len by simp
    show ?thesis
      using False m_lt k_lt_total idx i_m_lt_len a_k_lt_len
            k_lt_drop_a m_lt_drop_i
      by (simp add: nth_append add.commute)
  qed
qed

lemma heap_bytes_word_append_between:
  fixes a i j :: "32 word"
  assumes a_le_i: "a \<le> i"
      and i_le_j: "i \<le> j"
  shows "heap_bytes_word s buf a (i - a) @
         heap_bytes_word s buf i (j - i) =
         heap_bytes_word s buf a (j - a)"
proof -
  have a_le_j: "a \<le> j"
    using a_le_i i_le_j by simp
  have h_ai:
    "heap_bytes_word s buf a (i - a) =
     take (unat (i - a)) (drop (unat a)
       (heap_bytes_word s buf 0 j))"
    by (rule heap_bytes_word_zero_take_drop_between[OF a_le_i i_le_j])
  have h_ij:
    "heap_bytes_word s buf i (j - i) =
     take (unat (j - i)) (drop (unat i)
       (heap_bytes_word s buf 0 j))"
    by (rule heap_bytes_word_zero_take_drop_between[OF i_le_j order.refl])
  have h_aj:
    "heap_bytes_word s buf a (j - a) =
     take (unat (j - a)) (drop (unat a)
       (heap_bytes_word s buf 0 j))"
    by (rule heap_bytes_word_zero_take_drop_between[OF a_le_j order.refl])
  have list:
    "take (unat i - unat a) (drop (unat a)
       (heap_bytes_word s buf 0 j)) @
     take (unat j - unat i) (drop (unat i)
       (heap_bytes_word s buf 0 j)) =
     take (unat j - unat a) (drop (unat a)
       (heap_bytes_word s buf 0 j))"
    by (rule take_drop_append_between)
       (use a_le_i i_le_j in
        \<open>simp_all add: word_le_nat_alt\<close>)
  show ?thesis
    using h_ai h_ij h_aj list a_le_i i_le_j a_le_j
    by (simp add: unat_sub word_le_nat_alt)
qed

lemma flush_pending_groups_run_from_heap_scan:
  fixes i j len :: "32 word"
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and min_len: "min_run \<le> unat (j - i)"
      and all_eq: "\<And>k. \<lbrakk> unat i \<le> k; k < unat j \<rbrakk> \<Longrightarrow>
        heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      and stop: "j < len \<Longrightarrow>
        heap_w8 s (pending +\<^sub>p uint j) \<noteq> b"
  shows "flush_pending_groups add
          (drop (unat i) (heap_bytes_word s pending 0 len)) =
         append_add_inst add [] @ [RRun b (unat (j - i))] @
         flush_pending_groups []
          (drop (unat j) (heap_bytes_word s pending 0 len))"
proof -
  have diff: "unat j - unat i = unat (j - i)"
    using i_lt_j by (simp add: unat_sub word_less_nat_alt word_le_nat_alt)
  have groups:
    "flush_pending_groups add
      (drop (unat i) (heap_bytes_word s pending 0 len)) =
     append_add_inst add [] @ [RRun b (unat j - unat i)] @
     flush_pending_groups []
      (drop (unat j) (heap_bytes_word s pending 0 len))"
  proof (rule flush_pending_groups_run_from_maximal)
    show "unat i < unat j"
      using i_lt_j by (simp add: word_less_nat_alt)
    show "unat j \<le> length (heap_bytes_word s pending 0 len)"
      using j_le_len by (simp add: word_le_nat_alt)
    show "min_run \<le> unat j - unat i"
      using diff min_len by simp
  next
    fix k
    assume i_le_k: "unat i \<le> k" and k_lt_j: "k < unat j"
    then have k_lt_len: "k < unat len"
      using j_le_len by (simp add: word_le_nat_alt)
    show "heap_bytes_word s pending 0 len ! k = b"
      using all_eq[OF i_le_k k_lt_j] k_lt_len
      by (simp add: heap_bytes_word_nth)
  next
    assume j_lt_len_nat: "unat j < length (heap_bytes_word s pending 0 len)"
    then have j_lt_len: "j < len"
      by (simp add: word_less_nat_alt)
    show "heap_bytes_word s pending 0 len ! unat j \<noteq> b"
      using stop[OF j_lt_len] j_lt_len_nat
      by (simp add: heap_bytes_word_nth word_unat.Rep_inverse)
  qed
  show ?thesis
    using groups diff by simp
qed

lemma flush_pending_groups_short_from_heap_scan:
  fixes i j len :: "32 word"
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and short: "unat (j - i) < min_run"
      and all_eq: "\<And>k. \<lbrakk> unat i \<le> k; k < unat j \<rbrakk> \<Longrightarrow>
        heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      and stop: "j < len \<Longrightarrow>
        heap_w8 s (pending +\<^sub>p uint j) \<noteq> b"
  shows "flush_pending_groups add
          (drop (unat i) (heap_bytes_word s pending 0 len)) =
         flush_pending_groups
          (add @ take (unat (j - i))
            (drop (unat i) (heap_bytes_word s pending 0 len)))
          (drop (unat j) (heap_bytes_word s pending 0 len))"
proof -
  have diff: "unat j - unat i = unat (j - i)"
    using i_lt_j by (simp add: unat_sub word_less_nat_alt word_le_nat_alt)
  have groups:
    "flush_pending_groups add
      (drop (unat i) (heap_bytes_word s pending 0 len)) =
     flush_pending_groups
      (add @ take (unat j - unat i)
        (drop (unat i) (heap_bytes_word s pending 0 len)))
      (drop (unat j) (heap_bytes_word s pending 0 len))"
  proof (rule flush_pending_groups_short_from_maximal)
    show "unat i < unat j"
      using i_lt_j by (simp add: word_less_nat_alt)
    show "unat j \<le> length (heap_bytes_word s pending 0 len)"
      using j_le_len by (simp add: word_le_nat_alt)
    show "unat j - unat i < min_run"
      using diff short by simp
  next
    fix k
    assume i_le_k: "unat i \<le> k" and k_lt_j: "k < unat j"
    then have k_lt_len: "k < unat len"
      using j_le_len by (simp add: word_le_nat_alt)
    show "heap_bytes_word s pending 0 len ! k = b"
      using all_eq[OF i_le_k k_lt_j] k_lt_len
      by (simp add: heap_bytes_word_nth)
  next
    assume j_lt_len_nat: "unat j < length (heap_bytes_word s pending 0 len)"
    then have j_lt_len: "j < len"
      by (simp add: word_less_nat_alt)
    show "heap_bytes_word s pending 0 len ! unat j \<noteq> b"
      using stop[OF j_lt_len] j_lt_len_nat
      by (simp add: heap_bytes_word_nth word_unat.Rep_inverse)
  qed
  show ?thesis
    using groups diff by simp
qed

lemma flush_pending_groups_short_heap_slice_update:
  fixes add_start i j len :: "32 word"
  assumes add_start_le_i: "add_start \<le> i"
      and i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and short: "unat (j - i) < min_run"
      and all_eq: "\<And>k. \<lbrakk> unat i \<le> k; k < unat j \<rbrakk> \<Longrightarrow>
        heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      and stop: "j < len \<Longrightarrow>
        heap_w8 s (pending +\<^sub>p uint j) \<noteq> b"
  shows "flush_pending_groups
          (heap_bytes_word s pending add_start (i - add_start))
          (drop (unat i) (heap_bytes_word s pending 0 len)) =
         flush_pending_groups
          (heap_bytes_word s pending add_start (j - add_start))
          (drop (unat j) (heap_bytes_word s pending 0 len))"
proof -
  have i_le_j: "i \<le> j"
    using i_lt_j by simp
  have short_branch:
    "flush_pending_groups
      (heap_bytes_word s pending add_start (i - add_start))
      (drop (unat i) (heap_bytes_word s pending 0 len)) =
     flush_pending_groups
      (heap_bytes_word s pending add_start (i - add_start) @
       take (unat (j - i))
        (drop (unat i) (heap_bytes_word s pending 0 len)))
      (drop (unat j) (heap_bytes_word s pending 0 len))"
    by (rule flush_pending_groups_short_from_heap_scan[
      OF i_lt_j j_le_len short all_eq stop])
  have scanned:
    "take (unat (j - i))
      (drop (unat i) (heap_bytes_word s pending 0 len)) =
     heap_bytes_word s pending i (j - i)"
    using i_le_j j_le_len
    by (simp add: heap_bytes_word_zero_take_drop_between)
  have appended:
    "heap_bytes_word s pending add_start (i - add_start) @
     heap_bytes_word s pending i (j - i) =
     heap_bytes_word s pending add_start (j - add_start)"
    by (rule heap_bytes_word_append_between[OF add_start_le_i i_le_j])
  show ?thesis
    using short_branch scanned appended by simp
qed

lemma flush_pending_groups_run_from_heap_scan_word:
  fixes i j len :: "32 word"
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and run_ge: "(4 :: 32 word) \<le> j - i"
      and all_eq: "\<And>k. \<lbrakk> unat i \<le> k; k < unat j \<rbrakk> \<Longrightarrow>
        heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      and stop: "j < len \<Longrightarrow>
        heap_w8 s (pending +\<^sub>p uint j) \<noteq> b"
  shows "flush_pending_groups add
          (drop (unat i) (heap_bytes_word s pending 0 len)) =
         append_add_inst add [] @ [RRun b (unat (j - i))] @
         flush_pending_groups []
          (drop (unat j) (heap_bytes_word s pending 0 len))"
proof -
  have min_len: "min_run \<le> unat (j - i)"
    using run_ge by (simp add: min_run_def word_le_nat_alt)
  show ?thesis
    by (rule flush_pending_groups_run_from_heap_scan[
      OF i_lt_j j_le_len min_len all_eq stop])
qed

lemma flush_pending_groups_short_heap_slice_update_word:
  fixes add_start i j len :: "32 word"
  assumes add_start_le_i: "add_start \<le> i"
      and i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and short: "\<not> (4 :: 32 word) \<le> j - i"
      and all_eq: "\<And>k. \<lbrakk> unat i \<le> k; k < unat j \<rbrakk> \<Longrightarrow>
        heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      and stop: "j < len \<Longrightarrow>
        heap_w8 s (pending +\<^sub>p uint j) \<noteq> b"
  shows "flush_pending_groups
          (heap_bytes_word s pending add_start (i - add_start))
          (drop (unat i) (heap_bytes_word s pending 0 len)) =
         flush_pending_groups
          (heap_bytes_word s pending add_start (j - add_start))
          (drop (unat j) (heap_bytes_word s pending 0 len))"
proof -
  have short_nat: "unat (j - i) < min_run"
    using short by (simp add: min_run_def word_le_nat_alt)
  show ?thesis
    by (rule flush_pending_groups_short_heap_slice_update[
      OF add_start_le_i i_lt_j j_le_len short_nat all_eq stop])
qed

lemma length_takeWhile_le_self:
  "length (takeWhile P xs) \<le> length xs"
  by (induction xs) auto

lemma take_length_takeWhile:
  "take (length (takeWhile P xs)) xs = takeWhile P xs"
  by (induction xs) auto

definition pending_slice :: "byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> byte list" where
  "pending_slice pending a b = take (b - a) (drop a pending)"

definition pending_run_end :: "byte list \<Rightarrow> nat \<Rightarrow> nat" where
  "pending_run_end pending i =
     (let b = pending ! i in
      i + length (takeWhile ((=) b) (drop i pending)))"

definition flush_pending_emit_add_spec ::
  "nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   enc_full_state \<Rightarrow> enc_full_state" where
  "flush_pending_emit_add_spec src_len pending add_start i st =
     (if add_start < i
      then emit_inst_spec src_len
        (RAdd (pending_slice pending add_start i)) st
      else st)"

definition flush_pending_emit_run_spec ::
  "nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   enc_full_state \<Rightarrow> enc_full_state" where
  "flush_pending_emit_run_spec src_len pending i j st =
     emit_inst_spec src_len (RRun (pending ! i) (j - i)) st"

lemma pending_run_end_gt:
  assumes i_lt_len: "i < length pending"
  shows "i < pending_run_end pending i"
proof -
  have drop_i:
    "drop i pending = pending ! i # drop (Suc i) pending"
    using Cons_nth_drop_Suc[OF i_lt_len] by simp
  show ?thesis
    using drop_i by (simp add: pending_run_end_def)
qed

lemma pending_run_end_le:
  assumes i_lt_len: "i < length pending"
  shows "pending_run_end pending i \<le> length pending"
proof -
  let ?tw = "takeWhile ((=) (pending ! i)) (drop i pending)"
  have "length ?tw \<le> length (drop i pending)"
    by (rule length_takeWhile_le_self)
  then have "length ?tw \<le> length pending - i"
    by simp
  then show ?thesis
    using i_lt_len by (simp add: pending_run_end_def)
qed

lemma pending_run_end_diff:
  assumes i_lt_len: "i < length pending"
  shows "pending_run_end pending i - i =
         length (takeWhile ((=) (pending ! i)) (drop i pending))"
  using pending_run_end_gt[OF i_lt_len]
  by (simp add: pending_run_end_def)

function flush_pending_loop_spec ::
  "nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   enc_full_state \<Rightarrow> enc_full_state" where
  "flush_pending_loop_spec src_len pending add_start i st =
     (if i < length pending then
        (let j = pending_run_end pending i in
         if min_run \<le> j - i
         then flush_pending_loop_spec src_len pending j j
           (flush_pending_emit_run_spec src_len pending i j
             (flush_pending_emit_add_spec src_len pending add_start i st))
         else flush_pending_loop_spec src_len pending add_start j st)
      else
        (flush_pending_emit_add_spec src_len pending add_start
          (length pending) st)\<lparr>enc_pending := []\<rparr>)"
  by pat_completeness auto
termination
  apply (relation "measure
    (\<lambda>(src_len, pending, add_start, i, st). length pending - i)")
   apply simp
  subgoal
    by (simp add: min_run_def)
  subgoal for src_len pending add_start i st
    using pending_run_end_gt[of i pending] pending_run_end_le[of i pending]
    by simp
  done

declare flush_pending_loop_spec.simps[simp del]

function flush_pending_loop_insts ::
  "byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> raw_inst list" where
  "flush_pending_loop_insts pending add_start i =
     (if i < length pending then
        (let j = pending_run_end pending i in
         if min_run \<le> j - i
         then append_add_inst (pending_slice pending add_start i) [] @
              [RRun (pending ! i) (j - i)] @
              flush_pending_loop_insts pending j j
         else flush_pending_loop_insts pending add_start j)
      else append_add_inst
        (pending_slice pending add_start (length pending)) [])"
  by pat_completeness auto
termination
  apply (relation "measure
    (\<lambda>(pending, add_start, i). length pending - i)")
   apply simp
  subgoal
    by (simp add: min_run_def)
  subgoal for pending add_start i
    using pending_run_end_gt[of i pending] pending_run_end_le[of i pending]
    by simp
  done

declare flush_pending_loop_insts.simps[simp del]

lemma pending_slice_empty_same[simp]:
  "pending_slice pending i i = []"
  by (simp add: pending_slice_def)

lemma pending_slice_append:
  assumes a_le_i: "a \<le> i"
      and i_le_j: "i \<le> j"
      and j_le_len: "j \<le> length pending"
  shows "pending_slice pending a i @ pending_slice pending i j =
         pending_slice pending a j"
  unfolding pending_slice_def
  by (rule take_drop_append_between[OF a_le_i i_le_j j_le_len])

lemma pending_slice_heap_bytes_word:
  fixes a i len :: "32 word"
  assumes a_le_i: "a \<le> i"
      and i_le_len: "i \<le> len"
  shows "pending_slice (heap_bytes_word s pending 0 len)
          (unat a) (unat i) =
         heap_bytes_word s pending a (i - a)"
proof -
  have slice:
    "heap_bytes_word s pending a (i - a) =
     take (unat (i - a))
       (drop (unat a) (heap_bytes_word s pending 0 len))"
    by (rule heap_bytes_word_zero_take_drop_between[OF a_le_i i_le_len])
  show ?thesis
    using slice a_le_i
    by (simp add: pending_slice_def unat_sub word_le_nat_alt)
qed

lemma flush_pending_emit_add_spec_heap_word:
  fixes add_start i len :: "32 word"
  assumes add_start_le_i: "add_start \<le> i"
      and i_le_len: "i \<le> len"
  shows "flush_pending_emit_add_spec src_len
          (heap_bytes_word s pending 0 len) (unat add_start) (unat i) st =
         (if add_start < i
          then emit_inst_spec src_len
            (RAdd (heap_bytes_word s pending add_start (i - add_start))) st
          else st)"
proof (cases "add_start < i")
  case True
  then have add_start_lt_i_nat: "unat add_start < unat i"
    by (simp add: word_less_nat_alt)
  have slice:
    "pending_slice (heap_bytes_word s pending 0 len)
      (unat add_start) (unat i) =
     heap_bytes_word s pending add_start (i - add_start)"
    by (rule pending_slice_heap_bytes_word[
      OF add_start_le_i i_le_len])
  show ?thesis
    using True add_start_lt_i_nat slice
    by (simp add: flush_pending_emit_add_spec_def)
next
  case False
  then have "\<not> unat add_start < unat i"
    by (simp add: word_less_nat_alt)
  then show ?thesis
    using False by (simp add: flush_pending_emit_add_spec_def)
qed

lemma flush_pending_emit_run_spec_heap_word:
  fixes i j len :: "32 word"
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
  shows "flush_pending_emit_run_spec src_len
          (heap_bytes_word s pending 0 len) (unat i) (unat j) st =
         emit_inst_spec src_len
          (RRun (heap_w8 s (pending +\<^sub>p uint i)) (unat (j - i))) st"
proof -
  have i_lt_len:
    "unat i < unat len"
    using i_lt_j j_le_len
    by (simp add: word_less_nat_alt word_le_nat_alt)
  have nth_i:
    "heap_bytes_word s pending 0 len ! unat i =
     heap_w8 s (pending +\<^sub>p uint i)"
    using heap_bytes_word_nth[OF i_lt_len, of s pending 0]
    by (simp add: word_unat.Rep_inverse)
  have diff:
    "unat j - unat i = unat (j - i)"
    using i_lt_j
    by (simp add: unat_sub word_less_nat_alt word_le_nat_alt)
  show ?thesis
    using nth_i diff
    by (simp add: flush_pending_emit_run_spec_def)
qed

lemma emit_insts_spec_append_add_pending_slice:
  assumes a_le_i: "a \<le> i"
      and i_le_len: "i \<le> length pending"
  shows "emit_insts_spec src_len
          (append_add_inst (pending_slice pending a i) []) st =
         flush_pending_emit_add_spec src_len pending a i st"
proof (cases "a < i")
  case True
  then have slice_nonempty:
    "pending_slice pending a i \<noteq> []"
    using i_le_len by (simp add: pending_slice_def)
  then show ?thesis
    using True by (simp add: flush_pending_emit_add_spec_def)
next
  case False
  then have "a = i"
    using a_le_i by simp
  then show ?thesis
    by (simp add: flush_pending_emit_add_spec_def)
qed

lemma emit_insts_spec_append_add_pending_slice_append:
  assumes a_le_i: "a \<le> i"
      and i_le_len: "i \<le> length pending"
  shows "emit_insts_spec src_len
          (append_add_inst (pending_slice pending a i) [] @ insts) st =
         emit_insts_spec src_len insts
          (flush_pending_emit_add_spec src_len pending a i st)"
proof -
  have base:
    "emit_insts_spec src_len
      (append_add_inst (pending_slice pending a i) []) st =
     flush_pending_emit_add_spec src_len pending a i st"
    by (rule emit_insts_spec_append_add_pending_slice[
      OF a_le_i i_le_len])
  show ?thesis
    using base by (simp only: emit_insts_spec_append)
qed

lemma emit_insts_spec_append_add_run_pending_slice:
  assumes a_le_i: "a \<le> i"
      and i_le_len: "i \<le> length pending"
  shows "emit_insts_spec src_len
          (append_add_inst (pending_slice pending a i) [] @
           [RRun (pending ! i) (j - i)] @ insts) st =
         emit_insts_spec src_len insts
          (flush_pending_emit_run_spec src_len pending i j
            (flush_pending_emit_add_spec src_len pending a i st))"
proof -
  have add_seq:
    "emit_insts_spec src_len
      (append_add_inst (pending_slice pending a i) [] @
       ([RRun (pending ! i) (j - i)] @ insts)) st =
     emit_insts_spec src_len ([RRun (pending ! i) (j - i)] @ insts)
      (flush_pending_emit_add_spec src_len pending a i st)"
    by (rule emit_insts_spec_append_add_pending_slice_append[
      OF a_le_i i_le_len])
  show ?thesis
    using add_seq
    by (simp add: flush_pending_emit_run_spec_def emit_insts_spec_def)
qed

lemma pending_run_end_dropWhile:
  assumes i_lt_len: "i < length pending"
  shows "dropWhile ((=) (pending ! i)) (drop i pending) =
         drop (pending_run_end pending i) pending"
proof -
  have drop_take:
    "dropWhile ((=) (pending ! i)) (drop i pending) =
     drop (length (takeWhile ((=) (pending ! i)) (drop i pending)))
       (drop i pending)"
    by (simp add: dropWhile_eq_drop)
  show ?thesis
    using drop_take by (simp add: pending_run_end_def drop_drop ac_simps)
qed

lemma pending_run_end_takeWhile:
  assumes i_lt_len: "i < length pending"
  shows "takeWhile ((=) (pending ! i)) (drop i pending) =
         pending_slice pending i (pending_run_end pending i)"
proof -
  let ?tw = "takeWhile ((=) (pending ! i)) (drop i pending)"
  have slice:
    "pending_slice pending i (pending_run_end pending i) =
     take (length ?tw) (drop i pending)"
    using pending_run_end_le[OF i_lt_len]
    by (simp add: pending_slice_def pending_run_end_def)
  have "take (length ?tw) (drop i pending) = ?tw"
    by (rule take_length_takeWhile)
  then show ?thesis
    using slice by simp
qed

lemma pending_run_end_eq_maximal:
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> length pending"
      and all_eq:
        "\<And>k. \<lbrakk> i \<le> k; k < j \<rbrakk> \<Longrightarrow>
          pending ! k = pending ! i"
      and stop:
        "j < length pending \<Longrightarrow> pending ! j \<noteq> pending ! i"
  shows "pending_run_end pending i = j"
proof -
  have tw:
    "takeWhile ((=) (pending ! i)) (drop i pending) =
     take (j - i) (drop i pending)"
    by (rule takeWhile_eq_take_maximal_from[
      OF i_lt_j j_le_len all_eq stop])
  have len_tw:
    "length (takeWhile ((=) (pending ! i)) (drop i pending)) = j - i"
    using tw i_lt_j j_le_len by simp
  show ?thesis
    using i_lt_j len_tw by (simp add: pending_run_end_def)
qed

lemma pending_run_end_eq_heap_scan:
  fixes i j len :: "32 word"
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and all_eq:
        "\<And>k. \<lbrakk> unat i \<le> k; k < unat j \<rbrakk> \<Longrightarrow>
          heap_w8 s
            (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) =
          heap_w8 s (pending +\<^sub>p uint i)"
      and stop:
        "j < len \<Longrightarrow>
          heap_w8 s (pending +\<^sub>p uint j) \<noteq>
          heap_w8 s (pending +\<^sub>p uint i)"
  shows "pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
         unat j"
proof (rule pending_run_end_eq_maximal)
  show "unat i < unat j"
    using i_lt_j by (simp add: word_less_nat_alt)
  show "unat j \<le> length (heap_bytes_word s pending 0 len)"
    using j_le_len by (simp add: word_le_nat_alt)
next
  fix k
  assume i_le_k: "unat i \<le> k" and k_lt_j: "k < unat j"
  then have k_lt_len: "k < unat len"
    using j_le_len by (simp add: word_le_nat_alt)
  have i_lt_len: "unat i < unat len"
    using i_lt_j j_le_len
    by (simp add: word_less_nat_alt word_le_nat_alt)
  show "heap_bytes_word s pending 0 len ! k =
        heap_bytes_word s pending 0 len ! unat i"
    using all_eq[OF i_le_k k_lt_j] k_lt_len i_lt_len
    by (simp add: heap_bytes_word_nth word_unat.Rep_inverse)
next
  assume j_lt_len_nat:
    "unat j < length (heap_bytes_word s pending 0 len)"
  then have j_lt_len: "j < len"
    by (simp add: word_less_nat_alt)
  have i_lt_len: "unat i < unat len"
    using i_lt_j j_le_len
    by (simp add: word_less_nat_alt word_le_nat_alt)
  show "heap_bytes_word s pending 0 len ! unat j \<noteq>
        heap_bytes_word s pending 0 len ! unat i"
    using stop[OF j_lt_len] j_lt_len_nat i_lt_len
    by (simp add: heap_bytes_word_nth word_unat.Rep_inverse)
qed

lemma flush_pending_groups_run_from_pending_run_end:
  assumes i_lt_len: "i < length pending"
      and run_ge: "min_run \<le> pending_run_end pending i - i"
  shows "flush_pending_groups add (drop i pending) =
         append_add_inst add [] @
         [RRun (pending ! i) (pending_run_end pending i - i)] @
         flush_pending_groups [] (drop (pending_run_end pending i) pending)"
proof -
  have drop_i:
    "drop i pending = pending ! i # drop (Suc i) pending"
    using Cons_nth_drop_Suc[OF i_lt_len] by simp
  have run_eq:
    "pending ! i # takeWhile ((=) (pending ! i)) (drop (Suc i) pending) =
     pending_slice pending i (pending_run_end pending i)"
    using pending_run_end_takeWhile[OF i_lt_len] drop_i by simp
  have rest_eq:
    "dropWhile ((=) (pending ! i)) (drop (Suc i) pending) =
     drop (pending_run_end pending i) pending"
    using pending_run_end_dropWhile[OF i_lt_len] drop_i by simp
  have run_len:
    "length (pending ! i # takeWhile ((=) (pending ! i))
       (drop (Suc i) pending)) =
     pending_run_end pending i - i"
    using pending_run_end_diff[OF i_lt_len] drop_i by simp
  show ?thesis
    using drop_i run_ge run_eq rest_eq run_len
    by (simp add: Let_def)
qed

lemma flush_pending_groups_short_from_pending_run_end:
  assumes i_lt_len: "i < length pending"
      and short: "pending_run_end pending i - i < min_run"
  shows "flush_pending_groups add (drop i pending) =
         flush_pending_groups
           (add @ pending_slice pending i (pending_run_end pending i))
           (drop (pending_run_end pending i) pending)"
proof -
  have drop_i:
    "drop i pending = pending ! i # drop (Suc i) pending"
    using Cons_nth_drop_Suc[OF i_lt_len] by simp
  have run_eq:
    "pending ! i # takeWhile ((=) (pending ! i)) (drop (Suc i) pending) =
     pending_slice pending i (pending_run_end pending i)"
    using pending_run_end_takeWhile[OF i_lt_len] drop_i by simp
  have rest_eq:
    "dropWhile ((=) (pending ! i)) (drop (Suc i) pending) =
     drop (pending_run_end pending i) pending"
    using pending_run_end_dropWhile[OF i_lt_len] drop_i by simp
  have run_len:
    "length (pending ! i # takeWhile ((=) (pending ! i))
       (drop (Suc i) pending)) =
     pending_run_end pending i - i"
    using pending_run_end_diff[OF i_lt_len] drop_i by simp
  show ?thesis
    using drop_i short run_eq rest_eq run_len
    by (simp add: Let_def)
qed

lemma flush_pending_loop_insts_eq_groups_aux:
  "\<forall>i add_start.
      fuel = length pending - i \<longrightarrow>
      add_start \<le> i \<longrightarrow>
      i \<le> length pending \<longrightarrow>
      flush_pending_loop_insts pending add_start i =
        flush_pending_groups
          (pending_slice pending add_start i) (drop i pending)"
proof (induction "fuel :: nat" rule: nat_less_induct)
  case (1 fuel)
  show ?case
  proof (intro allI impI)
    fix i add_start
    assume fuel_eq: "fuel = length pending - i"
       and add_start_le_i: "add_start \<le> i"
       and i_le_len: "i \<le> length pending"
    show "flush_pending_loop_insts pending add_start i =
      flush_pending_groups
        (pending_slice pending add_start i) (drop i pending)"
    proof (cases "i < length pending")
      case True
      let ?j = "pending_run_end pending i"
      have i_lt_j: "i < ?j"
        by (rule pending_run_end_gt[OF True])
      have j_le_len: "?j \<le> length pending"
        by (rule pending_run_end_le[OF True])
      have fuel_j_lt: "length pending - ?j < fuel"
        using fuel_eq i_lt_j j_le_len True by simp
      show ?thesis
      proof (cases "min_run \<le> ?j - i")
        case run_ge: True
        have IH:
          "flush_pending_loop_insts pending ?j ?j =
           flush_pending_groups
            (pending_slice pending ?j ?j) (drop ?j pending)"
          using "1.IH" fuel_j_lt j_le_len by auto
        have groups:
          "flush_pending_groups (pending_slice pending add_start i)
            (drop i pending) =
           append_add_inst (pending_slice pending add_start i) [] @
           [RRun (pending ! i) (?j - i)] @
           flush_pending_groups [] (drop ?j pending)"
          by (rule flush_pending_groups_run_from_pending_run_end[
            OF True run_ge])
        show ?thesis
          using IH groups
          by (subst flush_pending_loop_insts.simps)
             (simp add: True run_ge Let_def)
      next
        case run_lt: False
        have short: "?j - i < min_run"
          using run_lt by simp
        have add_start_le_j: "add_start \<le> ?j"
          using add_start_le_i i_lt_j by simp
        have IH:
          "flush_pending_loop_insts pending add_start ?j =
           flush_pending_groups
            (pending_slice pending add_start ?j) (drop ?j pending)"
          using "1.IH" fuel_j_lt add_start_le_j j_le_len
          by auto
        have groups:
          "flush_pending_groups (pending_slice pending add_start i)
            (drop i pending) =
           flush_pending_groups
            (pending_slice pending add_start i @ pending_slice pending i ?j)
            (drop ?j pending)"
          by (rule flush_pending_groups_short_from_pending_run_end[
            OF True short])
        have slice:
          "pending_slice pending add_start i @ pending_slice pending i ?j =
           pending_slice pending add_start ?j"
          by (rule pending_slice_append[OF add_start_le_i _ j_le_len])
             (use i_lt_j in simp)
        show ?thesis
          using IH groups slice
          by (subst flush_pending_loop_insts.simps)
             (simp add: True run_lt Let_def)
      qed
    next
      case False
      then have i_eq_len: "i = length pending"
        using i_le_len by simp
      show ?thesis
        using i_eq_len
        by (subst flush_pending_loop_insts.simps)
           (simp add: False)
    qed
qed
qed

lemma flush_pending_loop_insts_eq_groups:
  assumes add_start_le_i: "add_start \<le> i"
      and i_le_len: "i \<le> length pending"
  shows "flush_pending_loop_insts pending add_start i =
         flush_pending_groups
          (pending_slice pending add_start i) (drop i pending)"
  using flush_pending_loop_insts_eq_groups_aux[of "length pending - i" pending]
        add_start_le_i i_le_len
  by auto

lemma flush_pending_loop_spec_eq_insts_aux:
  "\<forall>i add_start st.
      fuel = length pending - i \<longrightarrow>
      add_start \<le> i \<longrightarrow>
      i \<le> length pending \<longrightarrow>
      flush_pending_loop_spec src_len pending add_start i st =
        (emit_insts_spec src_len
          (flush_pending_loop_insts pending add_start i) st)
          \<lparr>enc_pending := []\<rparr>"
proof (induction "fuel :: nat" rule: nat_less_induct)
  case (1 fuel)
  show ?case
  proof (intro allI impI)
    fix i add_start st
    assume fuel_eq: "fuel = length pending - i"
       and add_start_le_i: "add_start \<le> i"
       and i_le_len: "i \<le> length pending"
    show "flush_pending_loop_spec src_len pending add_start i st =
      (emit_insts_spec src_len
        (flush_pending_loop_insts pending add_start i) st)
        \<lparr>enc_pending := []\<rparr>"
    proof (cases "i < length pending")
      case True
      let ?j = "pending_run_end pending i"
      have i_lt_j: "i < ?j"
        by (rule pending_run_end_gt[OF True])
      have j_le_len: "?j \<le> length pending"
        by (rule pending_run_end_le[OF True])
      have fuel_j_lt: "length pending - ?j < fuel"
        using fuel_eq i_lt_j j_le_len True by simp
      show ?thesis
      proof (cases "min_run \<le> ?j - i")
        case run_ge: True
        let ?st' =
          "flush_pending_emit_run_spec src_len pending i ?j
            (flush_pending_emit_add_spec src_len pending add_start i st)"
        have IH:
          "flush_pending_loop_spec src_len pending ?j ?j ?st' =
           (emit_insts_spec src_len
             (flush_pending_loop_insts pending ?j ?j) ?st')
            \<lparr>enc_pending := []\<rparr>"
          using "1.IH" fuel_j_lt j_le_len by auto
        have spec_unfold:
          "flush_pending_loop_spec src_len pending add_start i st =
           flush_pending_loop_spec src_len pending ?j ?j ?st'"
          by (subst flush_pending_loop_spec.simps)
             (simp add: True run_ge Let_def)
        have insts_unfold:
          "flush_pending_loop_insts pending add_start i =
           append_add_inst (pending_slice pending add_start i) [] @
           [RRun (pending ! i) (?j - i)] @
           flush_pending_loop_insts pending ?j ?j"
          by (subst flush_pending_loop_insts.simps)
             (simp add: True run_ge Let_def)
        have emit_seq:
          "emit_insts_spec src_len
            (flush_pending_loop_insts pending add_start i) st =
           emit_insts_spec src_len
            (flush_pending_loop_insts pending ?j ?j) ?st'"
          using insts_unfold
                emit_insts_spec_append_add_run_pending_slice[
                  OF add_start_le_i i_le_len,
                  of src_len ?j "flush_pending_loop_insts pending ?j ?j" st]
          by simp
        show ?thesis
          using spec_unfold IH emit_seq by simp
      next
        case run_lt: False
        have add_start_le_j: "add_start \<le> ?j"
          using add_start_le_i i_lt_j by simp
        have IH:
          "flush_pending_loop_spec src_len pending add_start ?j st =
           (emit_insts_spec src_len
             (flush_pending_loop_insts pending add_start ?j) st)
            \<lparr>enc_pending := []\<rparr>"
          using "1.IH" fuel_j_lt add_start_le_j j_le_len by auto
        have spec_unfold:
          "flush_pending_loop_spec src_len pending add_start i st =
           flush_pending_loop_spec src_len pending add_start ?j st"
          by (subst flush_pending_loop_spec.simps)
             (simp add: True run_lt Let_def)
        have insts_unfold:
          "flush_pending_loop_insts pending add_start i =
           flush_pending_loop_insts pending add_start ?j"
          by (subst flush_pending_loop_insts.simps)
             (simp add: True run_lt Let_def)
        show ?thesis
          using spec_unfold IH insts_unfold by simp
      qed
    next
      case False
      then have i_eq_len: "i = length pending"
        using i_le_len by simp
      have spec_unfold:
        "flush_pending_loop_spec src_len pending add_start i st =
         (flush_pending_emit_add_spec src_len pending add_start
          (length pending) st)\<lparr>enc_pending := []\<rparr>"
        by (subst flush_pending_loop_spec.simps)
           (simp add: False)
      have insts_unfold:
        "flush_pending_loop_insts pending add_start i =
         append_add_inst
          (pending_slice pending add_start (length pending)) []"
        using i_eq_len
        by (subst flush_pending_loop_insts.simps)
           (simp add: False)
      have emit_tail:
        "emit_insts_spec src_len
          (append_add_inst
            (pending_slice pending add_start (length pending)) []) st =
         flush_pending_emit_add_spec src_len pending add_start
          (length pending) st"
        by (rule emit_insts_spec_append_add_pending_slice[
          OF _ order.refl])
           (use add_start_le_i i_eq_len in simp)
      show ?thesis
        using spec_unfold insts_unfold emit_tail by simp
    qed
  qed
qed

lemma flush_pending_loop_spec_eq_insts:
  assumes add_start_le_i: "add_start \<le> i"
      and i_le_len: "i \<le> length pending"
  shows "flush_pending_loop_spec src_len pending add_start i st =
        (emit_insts_spec src_len
          (flush_pending_loop_insts pending add_start i) st)
          \<lparr>enc_pending := []\<rparr>"
  using flush_pending_loop_spec_eq_insts_aux[
        of "length pending - i" pending src_len]
        add_start_le_i i_le_len
  by auto

lemma flush_pending_loop_spec_eq_groups:
  assumes add_start_le_i: "add_start \<le> i"
      and i_le_len: "i \<le> length pending"
  shows "flush_pending_loop_spec src_len pending add_start i st =
         (emit_insts_spec src_len
           (flush_pending_groups (pending_slice pending add_start i)
             (drop i pending)) st)\<lparr>enc_pending := []\<rparr>"
proof -
  have spec:
    "flush_pending_loop_spec src_len pending add_start i st =
     (emit_insts_spec src_len
      (flush_pending_loop_insts pending add_start i) st)
      \<lparr>enc_pending := []\<rparr>"
    by (rule flush_pending_loop_spec_eq_insts[
      OF add_start_le_i i_le_len])
  have insts:
    "flush_pending_loop_insts pending add_start i =
     flush_pending_groups
      (pending_slice pending add_start i) (drop i pending)"
    by (rule flush_pending_loop_insts_eq_groups[
      OF add_start_le_i i_le_len])
  show ?thesis
    using spec insts by simp
qed

lemma flush_pending_loop_spec_eq_flush_pending_spec:
  assumes pending_eq: "enc_pending st = pending"
  shows "flush_pending_loop_spec src_len pending 0 0 st =
         flush_pending_spec src_len st"
proof -
  have loop:
    "flush_pending_loop_spec src_len pending 0 0 st =
     (emit_insts_spec src_len
       (flush_pending_groups (pending_slice pending 0 0) pending) st)
      \<lparr>enc_pending := []\<rparr>"
    using flush_pending_loop_spec_eq_groups[of 0 0 pending src_len st]
    by simp
  show ?thesis
    using loop pending_eq
    by (simp add: flush_pending_spec_groups)
qed

declare flush_pending_loop_spec_eq_groups[enc_flush_simps]
declare flush_pending_loop_spec_eq_flush_pending_spec[enc_flush_simps]

lemma flush_pending_loop_spec_run_step:
  assumes i_lt_len: "i < length pending"
      and run_ge: "min_run \<le> pending_run_end pending i - i"
  shows "flush_pending_loop_spec src_len pending add_start i st =
         flush_pending_loop_spec src_len pending
          (pending_run_end pending i) (pending_run_end pending i)
          (flush_pending_emit_run_spec src_len pending i
            (pending_run_end pending i)
            (flush_pending_emit_add_spec src_len pending add_start i st))"
  by (subst flush_pending_loop_spec.simps)
     (simp add: i_lt_len run_ge Let_def)

lemma flush_pending_loop_spec_short_step:
  assumes i_lt_len: "i < length pending"
      and run_lt: "\<not> min_run \<le> pending_run_end pending i - i"
  shows "flush_pending_loop_spec src_len pending add_start i st =
         flush_pending_loop_spec src_len pending add_start
          (pending_run_end pending i) st"
  by (subst flush_pending_loop_spec.simps)
     (simp add: i_lt_len run_lt Let_def)

lemma flush_pending_loop_spec_exit:
  assumes i_ge_len: "\<not> i < length pending"
  shows "flush_pending_loop_spec src_len pending add_start i st =
         (flush_pending_emit_add_spec src_len pending add_start
          (length pending) st)\<lparr>enc_pending := []\<rparr>"
  by (subst flush_pending_loop_spec.simps)
     (simp add: i_ge_len)

lemma flush_pending_loop_spec_run_step_word:
  fixes i j len :: "32 word"
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and run_end:
        "pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
         unat j"
      and run_ge: "(4 :: 32 word) \<le> j - i"
  shows "flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          add_start (unat i) st =
         flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          (unat j) (unat j)
          (flush_pending_emit_run_spec src_len
            (heap_bytes_word s pending 0 len) (unat i) (unat j)
            (flush_pending_emit_add_spec src_len
              (heap_bytes_word s pending 0 len) add_start (unat i) st))"
proof -
  have i_lt_len:
    "unat i < length (heap_bytes_word s pending 0 len)"
    using i_lt_j j_le_len
    by (simp add: word_less_nat_alt word_le_nat_alt)
  have diff:
    "unat (j - i) = unat j - unat i"
    using i_lt_j
    by (simp add: unat_sub word_less_nat_alt word_le_nat_alt)
  have run_ge_nat:
    "min_run \<le>
     pending_run_end (heap_bytes_word s pending 0 len) (unat i) - unat i"
    using run_ge run_end diff
    by (simp add: min_run_def word_le_nat_alt)
  show ?thesis
    using flush_pending_loop_spec_run_step[OF i_lt_len run_ge_nat,
        of src_len add_start st] run_end
    by simp
qed

lemma flush_pending_loop_spec_short_step_word:
  fixes i j len :: "32 word"
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and run_end:
        "pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
         unat j"
      and short: "\<not> (4 :: 32 word) \<le> j - i"
  shows "flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          add_start (unat i) st =
         flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          add_start (unat j) st"
proof -
  have i_lt_len:
    "unat i < length (heap_bytes_word s pending 0 len)"
    using i_lt_j j_le_len
    by (simp add: word_less_nat_alt word_le_nat_alt)
  have diff:
    "unat (j - i) = unat j - unat i"
    using i_lt_j
    by (simp add: unat_sub word_less_nat_alt word_le_nat_alt)
  have run_lt_nat:
    "\<not> min_run \<le>
     pending_run_end (heap_bytes_word s pending 0 len) (unat i) - unat i"
    using short run_end diff
    by (auto simp: min_run_def word_le_nat_alt)
  show ?thesis
    using flush_pending_loop_spec_short_step[OF i_lt_len run_lt_nat,
        of src_len add_start st] run_end
    by simp
qed

lemma flush_pending_loop_spec_exit_word:
  fixes i len :: "32 word"
  assumes i_ge_len: "\<not> i < len"
  shows "flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          add_start (unat i) st =
         (flush_pending_emit_add_spec src_len
           (heap_bytes_word s pending 0 len) add_start (unat len) st)
          \<lparr>enc_pending := []\<rparr>"
  by (subst flush_pending_loop_spec.simps)
     (use i_ge_len in \<open>simp add: word_less_nat_alt\<close>)

lemma flush_pending_loop_spec_run_step_heap_emit_word:
  fixes add_start i j len :: "32 word"
  assumes add_start_le_i: "add_start \<le> i"
      and i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and run_end:
        "pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
         unat j"
      and run_ge: "(4 :: 32 word) \<le> j - i"
      and b_eq: "b = heap_w8 s (pending +\<^sub>p uint i)"
  shows "flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          (unat add_start) (unat i) st =
         flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          (unat j) (unat j)
          (emit_inst_spec src_len (RRun b (unat (j - i)))
            (if add_start < i
             then emit_inst_spec src_len
               (RAdd (heap_bytes_word s pending add_start
                 (i - add_start))) st
             else st))"
proof -
  have i_le_len: "i \<le> len"
    using i_lt_j j_le_len by simp
  have step:
    "flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
      (unat add_start) (unat i) st =
     flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
      (unat j) (unat j)
      (flush_pending_emit_run_spec src_len
        (heap_bytes_word s pending 0 len) (unat i) (unat j)
        (flush_pending_emit_add_spec src_len
          (heap_bytes_word s pending 0 len) (unat add_start) (unat i)
          st))"
    by (rule flush_pending_loop_spec_run_step_word[
      OF i_lt_j j_le_len run_end run_ge])
  have add_step:
    "flush_pending_emit_add_spec src_len
      (heap_bytes_word s pending 0 len) (unat add_start) (unat i) st =
     (if add_start < i
      then emit_inst_spec src_len
        (RAdd (heap_bytes_word s pending add_start (i - add_start))) st
      else st)"
    by (rule flush_pending_emit_add_spec_heap_word[
      OF add_start_le_i i_le_len])
  have run_step:
    "\<And>st'. flush_pending_emit_run_spec src_len
      (heap_bytes_word s pending 0 len) (unat i) (unat j) st' =
     emit_inst_spec src_len
      (RRun (heap_w8 s (pending +\<^sub>p uint i)) (unat (j - i))) st'"
    by (rule flush_pending_emit_run_spec_heap_word[
      OF i_lt_j j_le_len])
  show ?thesis
    using step add_step b_eq by (simp add: run_step)
qed

lemma flush_pending_loop_spec_short_step_heap_word:
  fixes i j len :: "32 word"
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and run_end:
        "pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
         unat j"
      and short: "\<not> (4 :: 32 word) \<le> j - i"
  shows "flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          add_start (unat i) st =
         flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          add_start (unat j) st"
  by (rule flush_pending_loop_spec_short_step_word[
    OF i_lt_j j_le_len run_end short])

lemma flush_pending_loop_spec_exit_heap_emit_word:
  fixes add_start i len :: "32 word"
  assumes add_start_le_len: "add_start \<le> len"
      and i_ge_len: "\<not> i < len"
  shows "flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
          (unat add_start) (unat i) st =
         ((if add_start < len
           then emit_inst_spec src_len
             (RAdd (heap_bytes_word s pending add_start
               (len - add_start))) st
           else st)\<lparr>enc_pending := []\<rparr>)"
proof -
  have exit:
    "flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
      (unat add_start) (unat i) st =
     (flush_pending_emit_add_spec src_len
       (heap_bytes_word s pending 0 len) (unat add_start) (unat len) st)
      \<lparr>enc_pending := []\<rparr>"
    by (rule flush_pending_loop_spec_exit_word[OF i_ge_len])
  have add_step:
    "flush_pending_emit_add_spec src_len
      (heap_bytes_word s pending 0 len) (unat add_start) (unat len) st =
     (if add_start < len
      then emit_inst_spec src_len
        (RAdd (heap_bytes_word s pending add_start
          (len - add_start))) st
      else st)"
    by (rule flush_pending_emit_add_spec_heap_word[
      OF add_start_le_len order.refl])
  show ?thesis
    using exit add_step by simp
qed

lemma flush_pending_insts_short:
  assumes len_lt: "length pending < min_run"
  shows "flush_pending_insts pending =
    (if pending = [] then [] else [RAdd pending])"
proof -
  have len_lt4: "length pending < 4"
    using len_lt by (simp add: min_run_def)
  show ?thesis
    using len_lt4
    apply (cases pending)
     apply (simp add: flush_pending_insts_def append_add_inst_def
                      close_pending_run_def pending_scan_init_def)
    subgoal for b pending'
      apply (cases pending')
       apply (simp add: flush_pending_insts_def append_add_inst_def
                        close_pending_run_def pending_scan_init_def
                        pending_scan_step_def min_run_def)
      subgoal for c pending''
        apply (cases pending'')
         apply (simp add: flush_pending_insts_def append_add_inst_def
                          close_pending_run_def pending_scan_init_def
                          pending_scan_step_def min_run_def)
        subgoal for d pending'''
          apply (cases pending''')
           apply (simp add: flush_pending_insts_def append_add_inst_def
                            close_pending_run_def pending_scan_init_def
                            pending_scan_step_def min_run_def)
          apply simp
          done
        done
      done
    done
qed

lemma flush_pending_spec_short:
  assumes len_lt: "length (enc_pending st) < min_run"
  shows "flush_pending_spec src_len st =
    (if enc_pending st = [] then st
     else (emit_inst_spec src_len (RAdd (enc_pending st)) st)
       \<lparr> enc_pending := [] \<rparr>)"
proof (cases "enc_pending st = []")
  case True
  then show ?thesis
    by (simp add: flush_pending_spec_def flush_pending_insts_def
                  emit_insts_spec_def append_add_inst_def
                  close_pending_run_def pending_scan_init_def)
next
  case False
  have insts:
    "flush_pending_insts (enc_pending st) = [RAdd (enc_pending st)]"
    using flush_pending_insts_short[OF len_lt] False by simp
  show ?thesis
    using False insts
    by (simp add: flush_pending_spec_def emit_insts_spec_def)
qed

lemma flush_pending_spec_short_nonempty_sections:
  assumes pending_nonempty: "enc_pending st \<noteq> []"
      and len_lt: "length (enc_pending st) < min_run"
  shows "enc_data (flush_pending_spec src_len st) =
          enc_data st @ enc_pending st"
    and "enc_inst (flush_pending_spec src_len st) =
          enc_inst st @ [word_of_nat (1 + length (enc_pending st))]"
    and "enc_addr (flush_pending_spec src_len st) = enc_addr st"
    and "enc_cache (flush_pending_spec src_len st) = enc_cache st"
    and "enc_flushed (flush_pending_spec src_len st) =
          enc_flushed st + length (enc_pending st)"
    and "enc_pending (flush_pending_spec src_len st) = []"
proof -
  have len_ge: "1 \<le> length (enc_pending st)"
    using pending_nonempty by (cases "enc_pending st") auto
  have len_le: "length (enc_pending st) \<le> 17"
    using len_lt by (simp add: min_run_def)
  have opcode:
    "find_single_add_opcode (length (enc_pending st)) =
      (1 + length (enc_pending st), False)"
    using len_ge len_le by (simp add: find_single_add_opcode_def)
  show "enc_data (flush_pending_spec src_len st) =
          enc_data st @ enc_pending st"
    using flush_pending_spec_short[OF len_lt] pending_nonempty opcode
    by (simp add: emit_inst_spec_def encode_one.simps Let_def)
  show "enc_inst (flush_pending_spec src_len st) =
          enc_inst st @ [word_of_nat (1 + length (enc_pending st))]"
    using flush_pending_spec_short[OF len_lt] pending_nonempty opcode
    by (simp add: emit_inst_spec_def encode_one.simps Let_def)
  show "enc_addr (flush_pending_spec src_len st) = enc_addr st"
    using flush_pending_spec_short[OF len_lt] pending_nonempty opcode
    by (simp add: emit_inst_spec_def encode_one.simps Let_def)
  show "enc_cache (flush_pending_spec src_len st) = enc_cache st"
    using flush_pending_spec_short[OF len_lt] pending_nonempty opcode
    by (simp add: emit_inst_spec_def encode_one.simps Let_def)
  show "enc_flushed (flush_pending_spec src_len st) =
          enc_flushed st + length (enc_pending st)"
    using flush_pending_spec_short[OF len_lt] pending_nonempty opcode
    by (simp add: emit_inst_spec_def encode_one.simps Let_def)
  show "enc_pending (flush_pending_spec src_len st) = []"
    using flush_pending_spec_short[OF len_lt] pending_nonempty opcode
    by (simp add: emit_inst_spec_def encode_one.simps Let_def)
qed

lemma flush_pending_spec_four_run:
  assumes pending_eq: "enc_pending st = [b, b, b, b]"
  shows "flush_pending_spec src_len st =
    (emit_inst_spec src_len (RRun b (4 :: nat)) st)\<lparr>enc_pending := []\<rparr>"
  using pending_eq
  by (simp add: flush_pending_spec_def flush_pending_insts_def
                pending_scan_init_def pending_scan_step_def
                close_pending_run_def append_add_inst_def
                emit_insts_spec_def min_run_def numeral_eq_Suc)

lemma flush_pending_spec_four_add_break1:
  assumes pending_eq: "enc_pending st = [b0, b1, b2, b3]"
      and break: "b1 \<noteq> b0"
  shows "flush_pending_spec src_len st =
    (emit_inst_spec src_len (RAdd [b0, b1, b2, b3]) st)\<lparr>enc_pending := []\<rparr>"
  using pending_eq break
  by (simp add: flush_pending_spec_def flush_pending_insts_def
                pending_scan_init_def pending_scan_step_def
                close_pending_run_def append_add_inst_def
                emit_insts_spec_def min_run_def numeral_eq_Suc)

lemma flush_pending_spec_four_add_break2:
  assumes pending_eq: "enc_pending st = [b, b, c, d]"
      and break: "c \<noteq> b"
  shows "flush_pending_spec src_len st =
    (emit_inst_spec src_len (RAdd [b, b, c, d]) st)\<lparr>enc_pending := []\<rparr>"
  using pending_eq break
  by (simp add: flush_pending_spec_def flush_pending_insts_def
                pending_scan_init_def pending_scan_step_def
                close_pending_run_def append_add_inst_def
                emit_insts_spec_def min_run_def numeral_eq_Suc)

lemma flush_pending_spec_four_add_break3:
  assumes pending_eq: "enc_pending st = [b, b, b, c]"
      and break: "c \<noteq> b"
  shows "flush_pending_spec src_len st =
    (emit_inst_spec src_len (RAdd [b, b, b, c]) st)\<lparr>enc_pending := []\<rparr>"
  using pending_eq break
  by (simp add: flush_pending_spec_def flush_pending_insts_def
                pending_scan_init_def pending_scan_step_def
                close_pending_run_def append_add_inst_def
                emit_insts_spec_def min_run_def numeral_eq_Suc)

lemma foldl_pending_scan_step_replicate_init_Suc:
  "foldl pending_scan_step pending_scan_init (replicate (Suc n) b) =
   pending_scan_init\<lparr>ps_run_byte := Some b, ps_run_len := Suc n\<rparr>"
  by (simp add: pending_scan_init_def pending_scan_step_def
                foldl_pending_scan_step_replicate_current)

lemma flush_pending_insts_replicate_run:
  assumes n_ge: "min_run \<le> n"
  shows "flush_pending_insts (replicate n b) = [RRun b n]"
proof (cases n)
  case 0
  then show ?thesis
    using n_ge by (simp add: min_run_def)
next
  case (Suc n')
  have fold:
    "foldl pending_scan_step pending_scan_init (replicate (Suc n') b) =
     pending_scan_init\<lparr>ps_run_byte := Some b, ps_run_len := Suc n'\<rparr>"
    by (rule foldl_pending_scan_step_replicate_init_Suc)
  then show ?thesis
    using Suc n_ge fold
    by (simp add: flush_pending_insts_def
                  close_pending_run_def append_add_inst_def
                  pending_scan_init_def emit_insts_spec_def)
qed

lemma flush_pending_spec_replicate_run:
  assumes pending_eq: "enc_pending st = replicate n b"
      and n_ge: "min_run \<le> n"
  shows "flush_pending_spec src_len st =
    (emit_inst_spec src_len (RRun b n) st)\<lparr>enc_pending := []\<rparr>"
  using pending_eq flush_pending_insts_replicate_run[OF n_ge]
  by (simp add: flush_pending_spec_def emit_insts_spec_def)

lemma flush_pending_spec_replicate_run_sections:
  assumes pending_eq: "enc_pending st = replicate n b"
      and n_ge: "min_run \<le> n"
  shows "enc_data (flush_pending_spec src_len st) =
          enc_data (emit_inst_spec src_len (RRun b n) st)"
    and "enc_inst (flush_pending_spec src_len st) =
          enc_inst (emit_inst_spec src_len (RRun b n) st)"
    and "enc_addr (flush_pending_spec src_len st) =
          enc_addr (emit_inst_spec src_len (RRun b n) st)"
  using flush_pending_spec_replicate_run[OF pending_eq n_ge]
  by simp_all

lemma enc_pending_heap_bytes_word_all_eq_replicate:
  assumes pending_eq:
        "enc_pending st = heap_bytes_word s pending 0 len"
      and all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
  shows "enc_pending st = replicate (unat len) (heap_w8 s pending)"
  using pending_eq heap_bytes_word_replicateI[of len s pending 0 "heap_w8 s pending"]
        all_eq
  by simp

lemma flush_pending_spec_heap_all_eq_run_sections:
  assumes pending_eq:
        "enc_pending st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
  shows "enc_data (flush_pending_spec src_len st) =
          enc_data (emit_inst_spec src_len
            (RRun (heap_w8 s pending) (unat len)) st)"
    and "enc_inst (flush_pending_spec src_len st) =
          enc_inst (emit_inst_spec src_len
            (RRun (heap_w8 s pending) (unat len)) st)"
    and "enc_addr (flush_pending_spec src_len st) =
          enc_addr (emit_inst_spec src_len
            (RRun (heap_w8 s pending) (unat len)) st)"
proof -
  have pending_replicate:
    "enc_pending st = replicate (unat len) (heap_w8 s pending)"
    by (rule enc_pending_heap_bytes_word_all_eq_replicate[
        OF pending_eq all_eq])
  have min_run_len: "min_run \<le> unat len"
    using len_ge by (simp add: min_run_def word_le_nat_alt)
  show "enc_data (flush_pending_spec src_len st) =
          enc_data (emit_inst_spec src_len
            (RRun (heap_w8 s pending) (unat len)) st)"
    by (rule flush_pending_spec_replicate_run_sections(1)
        [OF pending_replicate min_run_len])
  show "enc_inst (flush_pending_spec src_len st) =
          enc_inst (emit_inst_spec src_len
            (RRun (heap_w8 s pending) (unat len)) st)"
    by (rule flush_pending_spec_replicate_run_sections(2)
        [OF pending_replicate min_run_len])
  show "enc_addr (flush_pending_spec src_len st) =
          enc_addr (emit_inst_spec src_len
            (RRun (heap_w8 s pending) (unat len)) st)"
    by (rule flush_pending_spec_replicate_run_sections(3)
        [OF pending_replicate min_run_len])
qed

lemma flush_pending_spec_heap_all_eq_run:
  assumes pending_eq:
        "enc_pending st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
  shows "flush_pending_spec src_len st =
    (emit_inst_spec src_len (RRun (heap_w8 s pending) (unat len)) st)
      \<lparr>enc_pending := []\<rparr>"
proof -
  have pending_replicate:
    "enc_pending st = replicate (unat len) (heap_w8 s pending)"
    by (rule enc_pending_heap_bytes_word_all_eq_replicate[
        OF pending_eq all_eq])
  have min_run_len: "min_run \<le> unat len"
    using len_ge by (simp add: min_run_def word_le_nat_alt)
  show ?thesis
    by (rule flush_pending_spec_replicate_run[
        OF pending_replicate min_run_len])
qed

declare flush_pending_spec_empty_sections[enc_flush_simps]
declare flush_pending_spec_short[enc_flush_simps]
declare flush_pending_spec_short_nonempty_sections[enc_flush_simps]
declare flush_pending_spec_four_run[enc_flush_simps]
declare flush_pending_spec_four_add_break1[enc_flush_simps]
declare flush_pending_spec_four_add_break2[enc_flush_simps]
declare flush_pending_spec_four_add_break3[enc_flush_simps]
declare flush_pending_spec_replicate_run[enc_flush_simps]
declare flush_pending_spec_replicate_run_sections[enc_flush_simps]
declare flush_pending_spec_heap_all_eq_run_sections[enc_flush_simps]
declare flush_pending_spec_heap_all_eq_run[enc_flush_simps]

lemma write_byte'_heap_bytes_append_next_typing_preserves2_word:
  assumes pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and dist: "ptr_range_distinct buf (Suc (unat pos))"
      and disj1: "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
      and disj2: "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
      and word_disj: "\<forall>i < unat out3_len.
           out3 +\<^sub>p uint (out3_pos + of_nat i) \<noteq> buf +\<^sub>p uint pos"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + 1)) =
                   heap_bytes s buf (unat pos) @ [b] \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   heap_bytes_word t out3 out3_pos out3_len =
                   heap_bytes_word s out3 out3_pos out3_len \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append2:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes t buf (unat (pos + 1)) =
               heap_bytes s buf (unat pos) @ [b] \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_heap_bytes_append_next_typing_preserves2
      [OF pos_lt ptr_ok dist disj1 disj2])
  have pres3:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes_word t out3 out3_pos out3_len =
               heap_bytes_word s out3 out3_pos out3_len \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule runs_to_weaken[OF write_byte'_spec])
     apply (rule ptr_ok)
    using pos_lt word_disj
    by (auto simp: word_not_le heap_bytes_word_def fun_upd_apply)
  have combined:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes t buf (unat (pos + 1)) =
           heap_bytes s buf (unat pos) @ [b] \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes_word t out3 out3_pos out3_len =
           heap_bytes_word s out3 out3_pos out3_len \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append2 pres3 by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma write_byte'_heap_bytes_append_next_typing_preserves2_near_ptr:
  assumes pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and dist: "ptr_range_distinct buf (Suc (unat pos))"
      and disj1: "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
      and disj2: "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + 1)) =
                   heap_bytes s buf (unat pos) @ [b] \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   near_ptr_'' t = near_ptr_'' s \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append2:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes t buf (unat (pos + 1)) =
               heap_bytes s buf (unat pos) @ [b] \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_heap_bytes_append_next_typing_preserves2
      [OF pos_lt ptr_ok dist disj1 disj2])
  have near:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               near_ptr_'' t = near_ptr_'' s \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule runs_to_weaken[OF write_byte'_spec])
     apply (rule ptr_ok)
    using pos_lt by auto
  have combined:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes t buf (unat (pos + 1)) =
           heap_bytes s buf (unat pos) @ [b] \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           near_ptr_'' t = near_ptr_'' s \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append2 near by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma write_bytes_loop_preserves_near_ptr:
  fixes len pos src_off :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. i < len)
           (\<lambda>i. do {
              guard (\<lambda>st. ptr_valid (heap_typing st) (buf +\<^sub>p uint (pos + i)));
              guard (\<lambda>st. ptr_valid (heap_typing st) (src +\<^sub>p uint (src_off + i)));
              modify (heap_w8_update
                (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                         h (src +\<^sub>p uint (src_off + i)))));
              return (i + 1)
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result len \<and>
            near_ptr_'' t = near_ptr_'' s \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len \<and>
             near_ptr_'' st = near_ptr_'' s \<and>
             heap_typing st = heap_typing s"])
     subgoal by simp
     subgoal by unat_arith
    subgoal premises prems for i st
    proof -
      have len_le: "unat len \<le> unat i"
        using prems(1) by (simp add: word_less_nat_alt)
      have i_eq: "i = len"
        using prems(2) len_le by (metis antisym_conv word_unat.Rep_inject)
      show ?thesis
        using prems(2) i_eq by simp
    qed
  subgoal for i st
    using dst_valid[rule_format, of "unat i"]
          src_valid[rule_format, of "unat i"]
    by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                   word_less_nat_alt word_unat.Rep_inverse
             intro: unat_suc_le_of_word_less
                    unat_measure_decrease_of_word_less)
  done

lemma write_bytes'_success_preserves_near_ptr:
  assumes fits: "\<not> cap - pos < len"
      and dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   near_ptr_'' t = near_ptr_'' s \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  using fits
  apply blast
  apply (rule runs_to_weaken[
    OF write_bytes_loop_preserves_near_ptr[OF dst_valid src_valid]])
  by auto

lemma write_bytes'_success_heap_bytes_append_wordpos_preserves2_near_ptr:
  assumes fits: "\<not> cap - pos < len"
      and dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
      and dst_src_disj: "\<forall>i < unat len. \<forall>j < unat len.
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           src +\<^sub>p uint (src_off + of_nat j)"
      and dst_inj: "\<forall>i < unat len. \<forall>j < unat len.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
      and prefix_disj: "\<forall>k < unat pos. \<forall>i.
           i < len \<longrightarrow> buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and no_overflow: "unat pos + unat len < 2 ^ 32"
      and disj1: "\<forall>k < out1_n. \<forall>i.
           i < len \<longrightarrow> out1 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and disj2: "\<forall>k < out2_n. \<forall>i.
           i < len \<longrightarrow> out2 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + len)) =
                   heap_bytes s buf (unat pos) @
                   heap_bytes_word s src src_off len \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   near_ptr_'' t = near_ptr_'' s \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append2:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes t buf (unat (pos + len)) =
               heap_bytes s buf (unat pos) @
               heap_bytes_word s src src_off len \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_heap_bytes_append_wordpos_preserves2
      [OF fits dst_valid src_valid dst_src_disj dst_inj prefix_disj
          no_overflow disj1 disj2])
  have near:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               near_ptr_'' t = near_ptr_'' s \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_preserves_near_ptr
      [OF fits dst_valid src_valid])
  have combined:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           heap_bytes t buf (unat (pos + len)) =
           heap_bytes s buf (unat pos) @
           heap_bytes_word s src src_off len \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           near_ptr_'' t = near_ptr_'' s \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append2 near by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma emit_add'_small_success_emitted_sections:
  assumes emitted:
        "emitted_sections s data inst addr sec data_bytes inst_bytes addr_bytes"
      and sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                emitted_sections t data inst addr sec'
                  (data_bytes @ heap_bytes_word s pending off sz)
                  (inst_bytes @ [ucast (1 + sz)])
                  addr_bytes) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.op_C (single_add_opcode' sz) = 1 + sz"
    "op_t_C.needs_size_C (single_add_opcode' sz) = 0"
    using single_add_opcode'_small[OF sz_ge sz_le] by auto
  show ?thesis
    unfolding emit_add'_def
    using op
    apply simp
    apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF write_byte'_heap_bytes_append_next_typing_preserves2_word])
          apply (rule inst_byte_fits)
         apply (rule inst_byte_ptr)
        apply (rule inst_byte_dist)
       apply (rule inst_byte_data_disj)
      apply (rule inst_byte_addr_disj)
     apply (rule inst_byte_pending_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_bytes'_success_heap_bytes_append_wordpos_preserves2])
           apply (rule data_fits)
          apply (clarsimp)
          using data_valid apply blast
         apply (clarsimp)
         using pending_valid apply blast
        apply (rule data_pending_disj)
       apply (rule data_inj)
      apply (rule data_prefix_disj)
     apply (rule data_no_overflow)
    apply (rule data_inst_disj)
    apply (rule data_addr_disj)
    apply (insert emitted)
    apply (clarsimp simp: sections_result_def emitted_sections_def sec_ok)
    done
qed

lemma emit_add'_small_success_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec src_len
                    (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?bs = "heap_bytes_word s pending off sz"
  have bs_len: "length ?bs = unat sz"
    by simp
  have pure_sections:
    "enc_data (emit_inst_spec src_len (RAdd ?bs) spec_st) =
       enc_data spec_st @ ?bs"
    "enc_inst (emit_inst_spec src_len (RAdd ?bs) spec_st) =
       enc_inst spec_st @ [ucast (1 + sz)]"
    "enc_addr (emit_inst_spec src_len (RAdd ?bs) spec_st) =
       enc_addr spec_st"
    using emit_inst_spec_RAdd_small_sections[OF sz_ge sz_le bs_len]
    by simp_all
  show ?thesis
    apply (rule runs_to_weaken[
      OF emit_add'_small_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] sz_ge sz_le sec_ok
            inst_byte_fits inst_byte_ptr inst_byte_dist
            inst_byte_data_disj inst_byte_addr_disj inst_byte_pending_disj
            data_fits data_valid pending_valid data_pending_disj data_inj
            data_prefix_disj data_no_overflow data_inst_disj
            data_addr_disj]])
    using pure_sections
    by (auto simp: enc_sections_state_rel_def)
qed

lemma emit_add'_small_success_preserves_heap_bytes_word:
  assumes sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and inst_byte_disj: "\<forall>i < unat out_len.
        out +\<^sub>p uint (out_pos + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_disj: "\<forall>k < unat out_len. \<forall>i.
        i < sz \<longrightarrow>
        out +\<^sub>p uint (out_pos + of_nat k) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK) \<and>
              heap_bytes_word t out out_pos out_len =
                heap_bytes_word s out out_pos out_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.op_C (single_add_opcode' sz) = 1 + sz"
    "op_t_C.needs_size_C (single_add_opcode' sz) = 0"
    using single_add_opcode'_small[OF sz_ge sz_le] by auto
  show ?thesis
    unfolding emit_add'_def
    using op
    apply simp
    apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF write_byte'_success_preserves_heap_bytes_word])
       apply (rule inst_byte_fits)
      apply (rule inst_byte_ptr)
     apply (rule inst_byte_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_bytes'_success_preserves_heap_bytes_word])
       apply (rule data_fits)
      apply (clarsimp)
      using data_valid apply blast
     apply (clarsimp)
     using pending_valid apply blast
    apply (rule data_disj)
    apply (simp add: sections_result_def sec_ok)
    done
qed

lemma emit_add'_large_success_preserves_typing:
  assumes sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.op_C (single_add_opcode' sz) = 1"
    "op_t_C.needs_size_C (single_add_opcode' sz) = 1"
    using single_add_opcode'_large[OF sz_large] by auto
  show ?thesis
    unfolding emit_add'_def
    using op
    apply simp
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_heap_bytes_word_single
          [OF inst_byte_fits inst_byte_ptr]])
     apply auto[1]
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_preserves_typing_bounded[where n = n])
        subgoal for t
          using size varint_size'_state_independent[of sz t s] by simp
       apply (rule inst_varint_fits)
      apply (intro allI impI)
      subgoal premises prems for t j
      proof -
        have ptr:
          "ptr_valid (heap_typing s)
            (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
          using inst_varint_valid prems by auto
        show ?thesis
          using ptr prems by simp
      qed
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_bytes'_success_preserves_typing])
      apply (rule data_fits)
     apply (clarsimp)
     using data_valid apply blast
    apply (clarsimp)
    using pending_valid apply blast
    apply (simp add: sections_result_def sec_ok)
    done
qed

lemma emit_add'_large_success_preserves_heap_bytes_word:
  assumes sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and inst_byte_disj: "\<forall>i < unat out_len.
        out +\<^sub>p uint (out_pos + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_disj: "\<forall>k < unat out_len. \<forall>i.
        i < n \<longrightarrow>
        out +\<^sub>p uint (out_pos + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_disj: "\<forall>k < unat out_len. \<forall>i.
        i < sz \<longrightarrow>
        out +\<^sub>p uint (out_pos + of_nat k) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK) \<and>
              heap_bytes_word t out out_pos out_len =
                heap_bytes_word s out out_pos out_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.op_C (single_add_opcode' sz) = 1"
    "op_t_C.needs_size_C (single_add_opcode' sz) = 1"
    using single_add_opcode'_large[OF sz_large] by auto
  show ?thesis
    unfolding emit_add'_def
    using op
    apply simp
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_preserves_heap_bytes_word])
        apply (rule inst_byte_fits)
       apply (rule inst_byte_ptr)
      apply (rule inst_byte_disj)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_preserves_heap_bytes_word_bounded
        [where n = n])
        subgoal for t
          using size varint_size'_state_independent[of sz t s] by simp
       apply (rule inst_varint_fits)
      apply (intro allI impI)
      subgoal premises prems for t j
      proof -
        have ptr:
          "ptr_valid (heap_typing s)
            (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
          using inst_varint_valid prems by auto
        show ?thesis
          using ptr prems by simp
      qed
     apply (rule inst_varint_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_bytes'_success_preserves_heap_bytes_word])
       apply (rule data_fits)
      apply (clarsimp)
      using data_valid apply blast
     apply (clarsimp)
     using pending_valid apply blast
    apply (rule data_disj)
    apply (simp add: sections_result_def sec_ok)
    done
qed

lemma emit_add'_large_success_emitted_sections:
  assumes emitted:
        "emitted_sections s data inst addr sec data_bytes inst_bytes addr_bytes"
      and sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_pending_disj: "\<forall>k < unat sz. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + n). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                emitted_sections t data inst addr sec'
                  (data_bytes @ heap_bytes_word s pending off sz)
                  (inst_bytes @ [1] @ varint_bytes32 sz n)
                  addr_bytes) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.op_C (single_add_opcode' sz) = 1"
    "op_t_C.needs_size_C (single_add_opcode' sz) = 1"
    using single_add_opcode'_large[OF sz_large] by auto
  show ?thesis
    unfolding emit_add'_def
    using op
    apply simp
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_heap_bytes_append_next_typing_preserves2_word])
           apply (rule inst_byte_fits)
          apply (rule inst_byte_ptr)
         apply (rule inst_byte_dist)
        apply (rule inst_byte_data_disj)
       apply (rule inst_byte_addr_disj)
      apply (rule inst_byte_pending_disj)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_heap_bytes_append_wordpos_preserves2_word
        [where n = n])
               subgoal for t
                 using size varint_size'_state_independent[of sz t s] by simp
              apply (rule inst_varint_fits)
             apply (intro allI impI)
             subgoal premises prems for t j
             proof -
               have ptr:
                 "ptr_valid (heap_typing s)
                   (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
                 using inst_varint_valid prems by auto
               show ?thesis
                 using ptr prems by simp
             qed
            apply (rule inst_varint_inj)
           apply (rule inst_varint_prefix_disj)
          apply (rule inst_varint_no_overflow)
         apply (rule inst_varint_data_disj)
        apply (rule inst_varint_addr_disj)
       apply (rule inst_varint_pending_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_bytes'_success_heap_bytes_append_wordpos_preserves2])
         apply (rule data_fits)
        apply (clarsimp)
        using data_valid apply blast
       apply (clarsimp)
       using pending_valid apply blast
      apply (rule data_pending_disj)
     apply (rule data_inj)
    apply (rule data_prefix_disj)
       apply (rule data_no_overflow)
      apply (rule data_inst_disj)
     apply (rule data_addr_disj)
    apply (insert emitted)
    apply (clarsimp simp: sections_result_def emitted_sections_def sec_ok)
    done
qed

lemma emit_add'_large_success_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_pending_disj: "\<forall>k < unat sz. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + n). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec src_len
                    (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?bs = "heap_bytes_word s pending off sz"
  have bs_len: "length ?bs = unat sz"
    by simp
  have pure_sections:
    "enc_data (emit_inst_spec src_len (RAdd ?bs) spec_st) =
       enc_data spec_st @ ?bs"
    "enc_inst (emit_inst_spec src_len (RAdd ?bs) spec_st) =
       enc_inst spec_st @ [1] @ varint_bytes32 sz n"
    "enc_addr (emit_inst_spec src_len (RAdd ?bs) spec_st) =
       enc_addr spec_st"
    using emit_inst_spec_RAdd_large_sections[OF sz_large bs_len size]
    by simp_all
  show ?thesis
    apply (rule runs_to_weaken[
      OF emit_add'_large_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] sz_large size sec_ok
            inst_byte_fits inst_byte_ptr inst_byte_dist
            inst_byte_data_disj inst_byte_addr_disj inst_byte_pending_disj
            inst_varint_fits inst_varint_valid inst_varint_inj
            inst_varint_prefix_disj inst_varint_no_overflow
            inst_varint_data_disj inst_varint_addr_disj
            inst_varint_pending_disj data_fits data_valid pending_valid
            data_pending_disj data_inj data_prefix_disj data_no_overflow
            data_inst_disj data_addr_disj]])
    using pure_sections
    by (auto simp: enc_sections_state_rel_def)
qed

lemma emit_run'_success_preserves_typing:
  assumes size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + 1)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_run'_def
  apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_heap_bytes_word_single
          [OF inst_byte_fits inst_byte_ptr]])
     apply auto[1]
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_preserves_typing_bounded[where n = n])
        subgoal for t
          using size varint_size'_state_independent[of sz t s] by simp
       apply (rule inst_varint_fits)
      apply (intro allI impI)
      subgoal premises prems for t j
      proof -
        have ptr:
          "ptr_valid (heap_typing s)
            (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
          using inst_varint_valid prems by auto
        show ?thesis
          using ptr prems by simp
      qed
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_byte'_success_heap_bytes_word_single])
      apply (rule data_byte_fits)
     apply (simp add: data_byte_ptr)
    apply auto[1]
   apply (simp add: sections_result_def sec_ok)
  done

lemma emit_run'_success_preserves_heap_bytes_word:
  assumes size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and inst_byte_disj: "\<forall>i < unat out_len.
        out +\<^sub>p uint (out_pos + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_disj: "\<forall>k < unat out_len. \<forall>i.
        i < n \<longrightarrow>
        out +\<^sub>p uint (out_pos + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_disj: "\<forall>i < unat out_len.
        out +\<^sub>p uint (out_pos + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + 1)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK) \<and>
              heap_bytes_word t out out_pos out_len =
                heap_bytes_word s out out_pos out_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_run'_def
  apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_preserves_heap_bytes_word])
        apply (rule inst_byte_fits)
       apply (rule inst_byte_ptr)
      apply (rule inst_byte_disj)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_preserves_heap_bytes_word_bounded
        [where n = n])
        subgoal for t
          using size varint_size'_state_independent[of sz t s] by simp
       apply (rule inst_varint_fits)
      apply (intro allI impI)
      subgoal premises prems for t j
      proof -
        have ptr:
          "ptr_valid (heap_typing s)
            (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
          using inst_varint_valid prems by auto
        show ?thesis
          using ptr prems by simp
      qed
     apply (rule inst_varint_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_byte'_success_preserves_heap_bytes_word])
      apply (rule data_byte_fits)
     apply (simp add: data_byte_ptr)
    apply (rule data_byte_disj)
   apply (simp add: sections_result_def sec_ok)
  done

lemma emit_run'_success_emitted_sections:
  assumes emitted:
        "emitted_sections s data inst addr sec data_bytes inst_bytes addr_bytes"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + 1)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                emitted_sections t data inst addr sec'
                  (data_bytes @ [fill])
                  (inst_bytes @ [0] @ varint_bytes32 sz n)
                  addr_bytes) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_run'_def
  apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_heap_bytes_append_next_typing_preserves2
          [OF inst_byte_fits inst_byte_ptr inst_byte_dist
              inst_byte_data_disj inst_byte_addr_disj]])
     apply (clarsimp simp: emitted_sections_def)
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_heap_bytes_append_wordpos_preserves2
        [where n = n])
              subgoal for t
                using size varint_size'_state_independent[of sz t s] by simp
             apply (rule inst_varint_fits)
            apply (intro allI impI)
            subgoal premises prems for t j
            proof -
              have ptr:
                "ptr_valid (heap_typing s)
                  (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
                using inst_varint_valid prems by auto
              show ?thesis
                using ptr prems by simp
            qed
           apply (rule inst_varint_inj)
          apply (rule inst_varint_prefix_disj)
         apply (rule inst_varint_no_overflow)
        apply (rule inst_varint_data_disj)
       apply (rule inst_varint_addr_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_byte'_heap_bytes_append_next_typing_preserves2])
         apply (rule data_byte_fits)
       apply (simp add: data_byte_ptr)
       apply (rule data_byte_dist)
      apply (rule data_byte_inst_disj)
     apply (rule data_byte_addr_disj)
    apply (insert emitted)
    apply (clarsimp simp: sections_result_def emitted_sections_def sec_ok emitted)
  done

lemma emit_run'_success_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + 1)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec src_len (RRun fill (unat sz)) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have pure_sections:
    "enc_data (emit_inst_spec src_len (RRun fill (unat sz)) spec_st) =
       enc_data spec_st @ [fill]"
    "enc_inst (emit_inst_spec src_len (RRun fill (unat sz)) spec_st) =
       enc_inst spec_st @ [0] @ varint_bytes32 sz n"
    "enc_addr (emit_inst_spec src_len (RRun fill (unat sz)) spec_st) =
       enc_addr spec_st"
    using emit_inst_spec_RRun_sections[OF size]
    by simp_all
  show ?thesis
    apply (rule runs_to_weaken[
      OF emit_run'_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] size sec_ok
            inst_byte_fits inst_byte_ptr inst_byte_dist
            inst_byte_data_disj inst_byte_addr_disj inst_varint_fits
            inst_varint_valid inst_varint_inj inst_varint_prefix_disj
            inst_varint_no_overflow inst_varint_data_disj
            inst_varint_addr_disj data_byte_fits data_byte_ptr
            data_byte_dist data_byte_inst_disj data_byte_addr_disj]])
    using pure_sections
    by (auto simp: enc_sections_state_rel_def)
qed

lemma emit_pending_add_chunk_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and sz_ge: "(1 :: 32 word) \<le> sz"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_pending_disj: "\<forall>k < unat sz. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj_small: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_inst_disj_large: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + n). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec src_len
                    (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof (cases "sz \<le> (17 :: 32 word)")
  case True
  have small:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_state_rel t data inst addr sec'
              (emit_inst_spec src_len
                (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_small_success_enc_sections_state_rel[
      OF rel sz_ge True sec_ok inst_byte_fits inst_byte_ptr
         inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
         inst_byte_pending_disj data_fits data_valid pending_valid
         data_pending_disj data_inj data_prefix_disj data_no_overflow
         data_inst_disj_small data_addr_disj])
  show ?thesis
    by (rule runs_to_weaken[OF small])
       (auto simp: sections_result_def)
next
  case False
  have large:
    "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
    using False by simp
  have add_large:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_state_rel t data inst addr sec'
              (emit_inst_spec src_len
                (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_large_success_enc_sections_state_rel[
      OF rel large size sec_ok inst_byte_fits inst_byte_ptr
         inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
         inst_byte_pending_disj inst_varint_fits inst_varint_valid
         inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
         inst_varint_data_disj inst_varint_addr_disj
         inst_varint_pending_disj data_fits data_valid pending_valid
         data_pending_disj data_inj data_prefix_disj data_no_overflow
         data_inst_disj_large data_addr_disj])
  show ?thesis
    by (rule runs_to_weaken[OF add_large])
       (auto simp: sections_result_def)
qed

lemma emit_pending_add_chunk_preserves_heap_bytes_word:
  assumes sz_ge: "(1 :: 32 word) \<le> sz"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and pending_frame_inst_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and pending_frame_inst_varint_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and pending_frame_data_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < sz \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof (cases "sz \<le> (17 :: 32 word)")
  case True
  have small:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec)
              ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_small_success_preserves_heap_bytes_word[
      OF sz_ge True sec_ok inst_byte_fits inst_byte_ptr data_fits
         data_valid pending_valid pending_frame_inst_byte_disj
         pending_frame_data_disj])
  show ?thesis
    by (rule runs_to_weaken[OF small])
       (auto simp: sections_result_def)
next
  case False
  have large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
    using False by simp
  have add_large:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_large_success_preserves_heap_bytes_word[
      OF large size sec_ok inst_byte_fits inst_byte_ptr
         inst_varint_fits inst_varint_valid data_fits data_valid
         pending_valid pending_frame_inst_byte_disj
         pending_frame_inst_varint_disj pending_frame_data_disj])
  show ?thesis
    by (rule runs_to_weaken[OF add_large])
       (auto simp: sections_result_def)
qed

lemma emit_pending_add_chunk_enc_sections_state_rel_preserves_heap_bytes_word:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and sz_ge: "(1 :: 32 word) \<le> sz"
      and size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_pending_disj: "\<forall>k < unat sz. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj_small: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_inst_disj_large: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + n). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and pending_frame_inst_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and pending_frame_inst_varint_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and pending_frame_data_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < sz \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec src_len
                    (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have state_rel:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            enc_sections_state_rel t data inst addr sec'
              (emit_inst_spec src_len
                (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_pending_add_chunk_enc_sections_state_rel[
      OF rel sz_ge size sec_ok inst_byte_fits inst_byte_ptr
         inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
         inst_byte_pending_disj inst_varint_fits inst_varint_valid
         inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
         inst_varint_data_disj inst_varint_addr_disj
         inst_varint_pending_disj data_fits data_valid pending_valid
         data_pending_disj data_inj data_prefix_disj data_no_overflow
         data_inst_disj_small data_inst_disj_large data_addr_disj])
  have pending_pres:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_t_C.err_C sec' = ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_pending_add_chunk_preserves_heap_bytes_word[
      OF sz_ge size sec_ok inst_byte_fits inst_byte_ptr inst_varint_fits
         inst_varint_valid data_fits data_valid pending_valid
         pending_frame_inst_byte_disj pending_frame_inst_varint_disj
         pending_frame_data_disj])
  have combined:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            enc_sections_state_rel t data inst addr sec'
              (emit_inst_spec src_len
                (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_t_C.err_C sec' = ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using state_rel pending_pres by (simp add: runs_to_conj)
  show ?thesis
    by (rule runs_to_weaken[OF combined]) auto
qed

lemma emit_pending_run_chunk_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
        \<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec src_len (RRun fill (unat sz)) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  obtain n where size: "varint_size' sz s = Some n"
    using varint_size'_some by blast
  have run:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + 1)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_state_rel t data inst addr sec'
              (emit_inst_spec src_len (RRun fill (unat sz)) spec_st)) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_run'_success_enc_sections_state_rel[
      OF rel size sec_ok inst_byte_fits inst_byte_ptr inst_byte_dist
         inst_byte_data_disj inst_byte_addr_disj
         inst_varint_fits[OF size] inst_varint_valid[OF size]
         inst_varint_inj[OF size] inst_varint_prefix_disj[OF size]
         inst_varint_no_overflow[OF size] inst_varint_data_disj[OF size]
         inst_varint_addr_disj[OF size] data_byte_fits data_byte_ptr
         data_byte_dist data_byte_inst_disj[OF size] data_byte_addr_disj])
  show ?thesis
    by (rule runs_to_weaken[OF run])
       (auto simp: sections_result_def)
qed

lemma emit_pending_run_chunk_preserves_heap_bytes_word:
  assumes size: "varint_size' sz s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and pending_frame_inst_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and pending_frame_inst_varint_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and pending_frame_data_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF emit_run'_success_preserves_heap_bytes_word[
      OF size sec_ok inst_byte_fits inst_byte_ptr inst_varint_fits
         inst_varint_valid data_byte_fits data_byte_ptr
         pending_frame_inst_byte_disj pending_frame_inst_varint_disj
         pending_frame_data_byte_disj]])
  by (auto simp: sections_result_def)

lemma emit_pending_run_chunk_enc_sections_state_rel_preserves_heap_bytes_word:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow> \<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
        \<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and pending_frame_inst_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and pending_frame_inst_varint_disj: "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
        \<forall>k < unat pending_frame_len. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and pending_frame_data_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec src_len (RRun fill (unat sz)) spec_st)) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  obtain n where size: "varint_size' sz s = Some n"
    using varint_size'_some by blast
  have state_rel:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            enc_sections_state_rel t data inst addr sec'
              (emit_inst_spec src_len (RRun fill (unat sz)) spec_st)) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_pending_run_chunk_enc_sections_state_rel[
      OF rel sec_ok inst_byte_fits inst_byte_ptr inst_byte_dist
         inst_byte_data_disj inst_byte_addr_disj inst_varint_fits
         inst_varint_valid inst_varint_inj inst_varint_prefix_disj
         inst_varint_no_overflow inst_varint_data_disj
         inst_varint_addr_disj data_byte_fits data_byte_ptr
         data_byte_dist data_byte_inst_disj data_byte_addr_disj])
  have pending_pres:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_t_C.err_C sec' = ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_pending_run_chunk_preserves_heap_bytes_word[
      OF size sec_ok inst_byte_fits inst_byte_ptr
         inst_varint_fits[OF size] inst_varint_valid[OF size]
         data_byte_fits data_byte_ptr pending_frame_inst_byte_disj
         pending_frame_inst_varint_disj[OF size]
         pending_frame_data_byte_disj])
  have combined:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            enc_sections_state_rel t data inst addr sec'
              (emit_inst_spec src_len (RRun fill (unat sz)) spec_st)) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_t_C.err_C sec' = ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using state_rel pending_pres by (simp add: runs_to_conj)
  show ?thesis
    by (rule runs_to_weaken[OF combined]) auto
qed

lemma emit_add'_small_success_enc_sections_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending off sz)
                  (inst_bytes @ [ucast (1 + sz)])
                  addr_bytes (target @ heap_bytes_word s pending off sz) c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?bs = "heap_bytes_word s pending off sz"
  have len32: "length ?bs < 2 ^ 32"
    using unat_lt2p[of sz] by simp
  have sz_nat_ge: "1 \<le> unat sz"
    using sz_ge by (simp add: word_le_nat_alt)
  have sz_nat_le: "unat sz \<le> 17"
    using sz_le by (simp add: word_le_nat_alt)
  have cast_eq: "(1 + word_of_nat (unat sz) :: byte) = ucast (1 + sz)"
  proof -
    have no32: "unat (1 + sz :: 32 word) = 1 + unat sz"
      using sz_nat_le by (simp add: unat_word_ariths)
    have ucast_unat: "unat (ucast (1 + sz) :: byte) = 1 + unat sz"
      using no32 sz_nat_le by (simp add: unat_ucast)
    have byte_unat: "unat ((1 :: byte) + word_of_nat (unat sz)) = 1 + unat sz"
    proof -
      have sz_lt256: "unat sz < 256"
        using sz_nat_le by simp
      have word_unat: "unat (word_of_nat (unat sz) :: byte) = unat sz"
        using sz_lt256 by (simp add: unat_ucast)
      have sum_lt: "1 + unat sz < 256"
        using sz_nat_le by simp
      show ?thesis
        using word_unat sum_lt by (simp add: unat_word_ariths)
    qed
    show ?thesis
      using byte_unat ucast_unat by (metis word_unat.Rep_inject)
  qed
  have inst_bytes_eq:
    "add_inst_bytes (length ?bs) = [ucast (1 + sz)]"
    using sz_nat_ge sz_nat_le cast_eq
    by (simp add: add_inst_bytes_def find_single_add_opcode_def)
  have decodes_post:
    "section_decodes src_seg tgt_len
      (data_bytes @ ?bs)
      (inst_bytes @ [ucast (1 + sz)])
      addr_bytes (target @ ?bs) c_out"
    using section_decodes_append_add
      [OF enc_sections_invD(2)[OF inv] len32]
          target_room inst_bytes_eq
    by simp
  show ?thesis
  apply (rule runs_to_weaken[
    OF emit_add'_small_success_emitted_sections
      [OF enc_sections_invD(1)[OF inv] sz_ge sz_le sec_ok inst_byte_fits
          inst_byte_ptr inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
          inst_byte_pending_disj data_fits data_valid pending_valid
          data_pending_disj data_inj data_prefix_disj data_no_overflow
          data_inst_disj data_addr_disj]])
  using decodes_post by (auto simp: enc_sections_inv_def)
qed

lemma emit_add'_small_success_enc_cache_abs:
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C (single_add_opcode' sz) = 0"
    using single_add_opcode'_small[OF sz_ge sz_le] by auto
  show ?thesis
    unfolding emit_add'_def
    using op
    apply simp
    apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF write_byte'_success_preserves_enc_cache_abs])
        apply (rule abs)
       apply (rule inst_byte_fits)
      apply (rule inst_byte_ptr)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_bytes'_success_preserves_enc_cache_abs])
       apply assumption
      apply (rule data_fits)
     apply (clarsimp)
     using data_valid apply blast
    apply (clarsimp)
    using pending_valid apply blast
    apply clarsimp
    apply runs_to_vcg
    using cache_wf by auto
qed

lemma emit_add'_small_success_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending off sz)
                  (inst_bytes @ [ucast (1 + sz)])
                  addr_bytes (target @ heap_bytes_word s pending off sz) c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have sections:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_inv t data inst addr sec' src_seg tgt_len
              (data_bytes @ heap_bytes_word s pending off sz)
              (inst_bytes @ [ucast (1 + sz)])
              addr_bytes (target @ heap_bytes_word s pending off sz) c_out) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_small_success_enc_sections_inv
      [OF inv sz_ge sz_le target_room sec_ok inst_byte_fits inst_byte_ptr
          inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
          inst_byte_pending_disj data_fits data_valid pending_valid
          data_pending_disj data_inj data_prefix_disj data_no_overflow
          data_inst_disj data_addr_disj])
  have cache:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_small_success_enc_cache_abs
      [OF abs cache_wf sz_ge sz_le inst_byte_fits inst_byte_ptr
          data_fits data_valid pending_valid])
  have combined:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_inv t data inst addr sec' src_seg tgt_len
              (data_bytes @ heap_bytes_word s pending off sz)
              (inst_bytes @ [ucast (1 + sz)])
              addr_bytes (target @ heap_bytes_word s pending off sz) c_out) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using sections cache by (simp add: runs_to_conj)
	  show ?thesis
	    apply (rule runs_to_weaken[OF combined])
	    by auto
	qed

lemma emit_add'_small_success_enc_sections_cache_pending_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and pending_frame_inst_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and pending_frame_data_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < sz \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending off sz)
                  (inst_bytes @ [ucast (1 + sz)])
                  addr_bytes (target @ heap_bytes_word s pending off sz) c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have sections_cache:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_inv t data inst addr sec' src_seg tgt_len
              (data_bytes @ heap_bytes_word s pending off sz)
              (inst_bytes @ [ucast (1 + sz)])
              addr_bytes (target @ heap_bytes_word s pending off sz) c_out \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_small_success_enc_sections_cache_inv
      [OF inv abs cache_wf sz_ge sz_le target_room sec_ok
          inst_byte_fits inst_byte_ptr inst_byte_dist inst_byte_data_disj
          inst_byte_addr_disj inst_byte_pending_disj data_fits data_valid
          pending_valid data_pending_disj data_inj data_prefix_disj
          data_no_overflow data_inst_disj data_addr_disj])
  have pending_pres:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec)
              ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_small_success_preserves_heap_bytes_word
      [OF sz_ge sz_le sec_ok inst_byte_fits inst_byte_ptr data_fits
          data_valid pending_valid pending_frame_inst_disj
          pending_frame_data_disj])
  have combined:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_inv t data inst addr sec' src_seg tgt_len
              (data_bytes @ heap_bytes_word s pending off sz)
              (inst_bytes @ [ucast (1 + sz)])
              addr_bytes (target @ heap_bytes_word s pending off sz) c_out \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec)
              ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using sections_cache pending_pres by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma emit_add'_large_success_enc_sections_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and size: "varint_size' sz s = Some n"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_pending_disj: "\<forall>k < unat sz. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + n). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending off sz)
                  (inst_bytes @ [1] @ varint_bytes32 sz n)
                  addr_bytes (target @ heap_bytes_word s pending off sz) c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?bs = "heap_bytes_word s pending off sz"
  have decodes_post:
    "section_decodes src_seg tgt_len
      (data_bytes @ ?bs)
      (inst_bytes @ [1] @ varint_bytes32 sz n)
      addr_bytes (target @ ?bs) c_out"
    by (rule section_decodes_append_add_cvarint
      [OF enc_sections_invD(2)[OF inv] size _ target_room])
       simp
  show ?thesis
  apply (rule runs_to_weaken[
    OF emit_add'_large_success_emitted_sections
      [OF enc_sections_invD(1)[OF inv] sz_large size sec_ok inst_byte_fits
          inst_byte_ptr inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
          inst_byte_pending_disj inst_varint_fits inst_varint_valid
          inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
          inst_varint_data_disj inst_varint_addr_disj inst_varint_pending_disj
          data_fits data_valid pending_valid data_pending_disj data_inj
          data_prefix_disj data_no_overflow data_inst_disj data_addr_disj]])
  using decodes_post by (auto simp: enc_sections_inv_def)
qed

lemma emit_add'_large_success_enc_cache_abs:
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and size: "varint_size' sz s = Some n"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.op_C (single_add_opcode' sz) = 1"
    "op_t_C.needs_size_C (single_add_opcode' sz) = 1"
    using single_add_opcode'_large[OF sz_large] by auto
  show ?thesis
    unfolding emit_add'_def
    using op
    apply simp
    apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF write_byte'_success_preserves_enc_cache_abs])
        apply (rule abs)
       apply (rule inst_byte_fits)
      apply (rule inst_byte_ptr)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken)
     apply (rule write_varint'_success_preserves_enc_cache_abs_bounded
       [where n = n])
        apply assumption
       subgoal for t
         using size varint_size'_state_independent[of sz t s] by simp
      apply (rule inst_varint_fits)
     apply (intro allI impI)
     subgoal premises prems for t j
     proof -
       have ptr:
         "ptr_valid (heap_typing s)
           (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
         using inst_varint_valid prems by auto
       show ?thesis
         using ptr prems by simp
     qed
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_bytes'_success_preserves_enc_cache_abs])
       apply assumption
      apply (rule data_fits)
     apply clarsimp
     using data_valid apply blast
    apply clarsimp
    using pending_valid apply blast
    apply clarsimp
    apply runs_to_vcg
    using cache_wf by auto
qed

lemma emit_add'_large_success_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and size: "varint_size' sz s = Some n"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_pending_disj: "\<forall>k < unat sz. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + n). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending off sz)
                  (inst_bytes @ [1] @ varint_bytes32 sz n)
                  addr_bytes (target @ heap_bytes_word s pending off sz) c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?section_post =
    "\<lambda>r t.
      (\<exists>sec'.
        r = Result sec' \<and>
        sections_result sec'
          (sections_t_C.data_pos_C sec + sz)
          (sections_t_C.inst_pos_C sec + 1 + n)
          (sections_t_C.addr_pos_C sec)
          ENC_OK \<and>
        enc_sections_inv t data inst addr sec' src_seg tgt_len
          (data_bytes @ heap_bytes_word s pending off sz)
          (inst_bytes @ [1] @ varint_bytes32 sz n)
          addr_bytes (target @ heap_bytes_word s pending off sz) c_out) \<and>
      heap_typing t = heap_typing s"
  let ?cache_post =
    "\<lambda>r t.
      (\<exists>sec'.
        r = Result sec' \<and>
        enc_cache_abs t c_out \<and>
        enc_cache_wf c_out) \<and>
      heap_typing t = heap_typing s"
  have sections:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> ?section_post \<rbrace>"
    by (rule emit_add'_large_success_enc_sections_inv
      [OF inv sz_large size target_room sec_ok inst_byte_fits
          inst_byte_ptr inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
          inst_byte_pending_disj inst_varint_fits inst_varint_valid
          inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
          inst_varint_data_disj inst_varint_addr_disj inst_varint_pending_disj
          data_fits data_valid pending_valid data_pending_disj data_inj
          data_prefix_disj data_no_overflow data_inst_disj data_addr_disj])
  have cache:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> ?cache_post \<rbrace>"
    by (rule emit_add'_large_success_enc_cache_abs
      [OF abs cache_wf sz_large size inst_byte_fits inst_byte_ptr
          inst_varint_fits inst_varint_valid data_fits data_valid
          pending_valid])
  have combined:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t. ?section_post r t \<and> ?cache_post r t \<rbrace>"
    using sections cache by (simp add: runs_to_conj)
	  show ?thesis
	    apply (rule runs_to_weaken[OF combined])
	    by auto
	qed

lemma emit_add'_large_success_enc_sections_cache_pending_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and sz_large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
      and size: "varint_size' sz s = Some n"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat sz.
           pending +\<^sub>p uint (off + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_pending_disj: "\<forall>k < unat sz. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      and data_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat sz.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (off + of_nat j))"
      and data_pending_disj: "\<forall>i < unat sz. \<forall>j < unat sz.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
      and data_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + n). \<forall>i.
        i < sz \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sz \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and pending_frame_inst_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and pending_frame_inst_varint_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and pending_frame_data_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < sz \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + sz)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending off sz)
                  (inst_bytes @ [1] @ varint_bytes32 sz n)
                  addr_bytes (target @ heap_bytes_word s pending off sz) c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have sections_cache:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_inv t data inst addr sec' src_seg tgt_len
              (data_bytes @ heap_bytes_word s pending off sz)
              (inst_bytes @ [1] @ varint_bytes32 sz n)
              addr_bytes (target @ heap_bytes_word s pending off sz) c_out \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_large_success_enc_sections_cache_inv
      [OF inv abs cache_wf sz_large size target_room sec_ok inst_byte_fits
          inst_byte_ptr inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
          inst_byte_pending_disj inst_varint_fits inst_varint_valid
          inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
          inst_varint_data_disj inst_varint_addr_disj inst_varint_pending_disj
          data_fits data_valid pending_valid data_pending_disj data_inj
          data_prefix_disj data_no_overflow data_inst_disj data_addr_disj])
  have pending_pres:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_large_success_preserves_heap_bytes_word
      [OF sz_large size sec_ok inst_byte_fits inst_byte_ptr
          inst_varint_fits inst_varint_valid data_fits data_valid
          pending_valid pending_frame_inst_byte_disj
          pending_frame_inst_varint_disj pending_frame_data_disj])
  have combined:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_inv t data inst addr sec' src_seg tgt_len
              (data_bytes @ heap_bytes_word s pending off sz)
              (inst_bytes @ [1] @ varint_bytes32 sz n)
              addr_bytes (target @ heap_bytes_word s pending off sz) c_out \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using sections_cache pending_pres by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma emit_run'_success_enc_sections_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and size: "varint_size' sz s = Some n"
      and sz_pos: "0 < unat sz"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + 1)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ [fill])
                  (inst_bytes @ [0] @ varint_bytes32 sz n)
                  addr_bytes (target @ replicate (unat sz) fill) c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have decodes_post:
    "section_decodes src_seg tgt_len
      (data_bytes @ [fill])
      (inst_bytes @ [0] @ varint_bytes32 sz n)
      addr_bytes (target @ replicate (unat sz) fill) c_out"
    by (rule section_decodes_append_run_cvarint
      [OF enc_sections_invD(2)[OF inv] size sz_pos target_room])
  show ?thesis
  apply (rule runs_to_weaken[
    OF emit_run'_success_emitted_sections
      [OF enc_sections_invD(1)[OF inv] size sec_ok inst_byte_fits
          inst_byte_ptr inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
          inst_varint_fits inst_varint_valid inst_varint_inj
          inst_varint_prefix_disj inst_varint_no_overflow
          inst_varint_data_disj inst_varint_addr_disj data_byte_fits
          data_byte_ptr data_byte_dist data_byte_inst_disj
          data_byte_addr_disj]])
  using decodes_post by (auto simp: enc_sections_inv_def)
qed

lemma emit_run'_success_enc_cache_abs:
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and size: "varint_size' sz s = Some n"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_run'_def
  apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_preserves_enc_cache_abs])
         apply (rule abs)
        apply (rule inst_byte_fits)
       apply (rule inst_byte_ptr)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_preserves_enc_cache_abs_bounded
        [where n = n])
         apply assumption
        subgoal for t
          using size varint_size'_state_independent[of sz t s] by simp
       apply (rule inst_varint_fits)
      apply (intro allI impI)
      subgoal premises prems for t j
      proof -
        have ptr:
          "ptr_valid (heap_typing s)
            (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
          using inst_varint_valid prems by auto
        show ?thesis
          using ptr prems by simp
      qed
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_byte'_success_preserves_enc_cache_abs])
       apply assumption
      apply (rule data_byte_fits)
     apply (simp add: data_byte_ptr)
    apply clarsimp
    apply runs_to_vcg
    using cache_wf by auto

lemma emit_run'_success_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and size: "varint_size' sz s = Some n"
      and sz_pos: "0 < unat sz"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + 1)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ [fill])
                  (inst_bytes @ [0] @ varint_bytes32 sz n)
                  addr_bytes (target @ replicate (unat sz) fill) c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?section_post =
    "\<lambda>r t.
      (\<exists>sec'.
        r = Result sec' \<and>
        sections_result sec'
          (sections_t_C.data_pos_C sec + 1)
          (sections_t_C.inst_pos_C sec + 1 + n)
          (sections_t_C.addr_pos_C sec)
          ENC_OK \<and>
        enc_sections_inv t data inst addr sec' src_seg tgt_len
          (data_bytes @ [fill])
          (inst_bytes @ [0] @ varint_bytes32 sz n)
          addr_bytes (target @ replicate (unat sz) fill) c_out) \<and>
      heap_typing t = heap_typing s"
  let ?cache_post =
    "\<lambda>r t.
      (\<exists>sec'.
        r = Result sec' \<and>
        enc_cache_abs t c_out \<and>
        enc_cache_wf c_out) \<and>
      heap_typing t = heap_typing s"
  have sections:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> ?section_post \<rbrace>"
    by (rule emit_run'_success_enc_sections_inv
      [OF inv size sz_pos target_room sec_ok inst_byte_fits
          inst_byte_ptr inst_byte_dist inst_byte_data_disj
          inst_byte_addr_disj inst_varint_fits inst_varint_valid
          inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
          inst_varint_data_disj inst_varint_addr_disj data_byte_fits
          data_byte_ptr data_byte_dist data_byte_inst_disj
          data_byte_addr_disj])
  have cache:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> ?cache_post \<rbrace>"
    by (rule emit_run'_success_enc_cache_abs
      [OF abs cache_wf size inst_byte_fits inst_byte_ptr
          inst_varint_fits inst_varint_valid data_byte_fits data_byte_ptr])
  have combined:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t. ?section_post r t \<and> ?cache_post r t \<rbrace>"
    using sections cache by (simp add: runs_to_conj)
	  show ?thesis
	    apply (rule runs_to_weaken[OF combined])
	    by auto
	qed

lemma emit_run'_success_enc_sections_cache_pending_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and size: "varint_size' sz s = Some n"
      and sz_pos: "0 < unat sz"
      and target_room:
        "length target + unat sz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and pending_frame_inst_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and pending_frame_inst_varint_disj: "\<forall>k < unat pending_frame_len. \<forall>i.
        i < n \<longrightarrow>
        pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and pending_frame_data_byte_disj: "\<forall>i < unat pending_frame_len.
        pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec + 1)
                  (sections_t_C.inst_pos_C sec + 1 + n)
                  (sections_t_C.addr_pos_C sec)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ [fill])
                  (inst_bytes @ [0] @ varint_bytes32 sz n)
                  addr_bytes (target @ replicate (unat sz) fill) c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have sections_cache:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + 1)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_inv t data inst addr sec' src_seg tgt_len
              (data_bytes @ [fill])
              (inst_bytes @ [0] @ varint_bytes32 sz n)
              addr_bytes (target @ replicate (unat sz) fill) c_out \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_run'_success_enc_sections_cache_inv
      [OF inv abs cache_wf size sz_pos target_room sec_ok inst_byte_fits
          inst_byte_ptr inst_byte_dist inst_byte_data_disj
          inst_byte_addr_disj inst_varint_fits inst_varint_valid
          inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
          inst_varint_data_disj inst_varint_addr_disj data_byte_fits
          data_byte_ptr data_byte_dist data_byte_inst_disj data_byte_addr_disj])
  have pending_pres:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + 1)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_run'_success_preserves_heap_bytes_word
      [OF size sec_ok inst_byte_fits inst_byte_ptr inst_varint_fits
          inst_varint_valid data_byte_fits data_byte_ptr
          pending_frame_inst_byte_disj pending_frame_inst_varint_disj
          pending_frame_data_byte_disj])
  have combined:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + 1)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK \<and>
            enc_sections_inv t data inst addr sec' src_seg tgt_len
              (data_bytes @ [fill])
              (inst_bytes @ [0] @ varint_bytes32 sz n)
              addr_bytes (target @ replicate (unat sz) fill) c_out \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + 1)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec)
              ENC_OK) \<and>
          heap_bytes_word t pending pending_frame_off pending_frame_len =
            heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using sections_cache pending_pres by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma gets_the_best_mode'_result:
  assumes "best_mode' copy_addr here s = Some m"
  shows "gets_the (best_mode' copy_addr here) \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and> r = Result m \<rbrace>"
  unfolding gets_the_def
  apply runs_to_vcg
  using assms by simp

lemma emit_copy'_small_addr_byte_success_emitted_sections:
  assumes emitted:
        "emitted_sections s data inst addr_buf sec data_bytes inst_bytes addr_bytes"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                emitted_sections t data inst addr_buf sec'
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
                  (addr_bytes @ [ucast (mode_t_C.arg_C m)])) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C
      (single_copy_opcode' copy_len (mode_t_C.mode_C m)) = 0"
    using single_copy_opcode'_small[OF sz_ge sz_le] by auto
  note gets_the_best_mode'_result[runs_to_vcg]
  show ?thesis
    unfolding emit_copy'_def
    using bm op
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: bm op)
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_heap_bytes_append_next_typing_preserves2_near_ptr])
           apply (rule inst_byte_fits)
          apply (rule inst_byte_ptr)
         apply (rule inst_byte_dist)
        apply (rule inst_byte_data_disj)
       apply (rule inst_byte_addr_disj)
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF emit_address'_success_byte_heap_bytes_append_preserves2_near_ptr])
            apply (rule mode_ge)
           apply (rule addr_byte_fits)
          apply (simp add: addr_byte_ptr)
         apply (rule addr_byte_dist)
        apply (rule addr_byte_data_disj)
       apply (rule addr_byte_inst_disj)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF cache_update'_preserves_heap_bytes3
        [of _ _ data "unat (sections_t_C.data_pos_C sec)"
           inst "unat (sections_t_C.inst_pos_C sec + 1)"
           addr_buf "unat (sections_t_C.addr_pos_C sec + 1)"]])
      using near_ptr_lt apply simp
    using emitted
    apply (clarsimp simp: sections_result_def emitted_sections_def sec_ok)
    done
qed

lemma emit_copy'_small_addr_varint_success_emitted_sections:
  assumes emitted:
        "emitted_sections s data inst addr_buf sec data_bytes inst_bytes addr_bytes"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                emitted_sections t data inst addr_buf sec'
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
                  (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C
      (single_copy_opcode' copy_len (mode_t_C.mode_C m)) = 0"
    using single_copy_opcode'_small[OF sz_ge sz_le] by auto
  note gets_the_best_mode'_result[runs_to_vcg]
  show ?thesis
    unfolding emit_copy'_def
    using bm op
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: bm op)
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_heap_bytes_append_next_typing_preserves2_near_ptr])
           apply (rule inst_byte_fits)
          apply (rule inst_byte_ptr)
         apply (rule inst_byte_dist)
        apply (rule inst_byte_data_disj)
       apply (rule inst_byte_addr_disj)
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken)
       apply (rule emit_address'_success_varint_heap_bytes_append_preserves2_near_ptr
        [where n = an])
              apply (rule mode_lt)
             subgoal for t
               using addr_size varint_size'_state_independent
                 [of "mode_t_C.arg_C m" t s] by simp
            apply (rule addr_varint_fits)
           apply (intro allI impI)
           subgoal premises prems for t j
           proof -
             have ptr:
               "ptr_valid (heap_typing s)
                 (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
               using addr_varint_valid prems by auto
             show ?thesis
               using ptr prems by simp
           qed
          apply (rule addr_varint_inj)
         apply (rule addr_varint_prefix_disj)
        apply (rule addr_varint_no_overflow)
       apply (rule addr_varint_data_disj)
      apply (rule addr_varint_inst_disj)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF cache_update'_preserves_heap_bytes3
        [of _ _ data "unat (sections_t_C.data_pos_C sec)"
           inst "unat (sections_t_C.inst_pos_C sec + 1)"
           addr_buf "unat (sections_t_C.addr_pos_C sec + an)"]])
      using near_ptr_lt apply simp
    using emitted
    apply (clarsimp simp: sections_result_def emitted_sections_def sec_ok)
    done
qed

lemma emit_copy'_large_addr_byte_success_emitted_sections:
  assumes emitted:
        "emitted_sections s data inst addr_buf sec data_bytes inst_bytes addr_bytes"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat sn. \<forall>j < unat sn.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat sn < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + sn).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1 + sn)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                emitted_sections t data inst addr_buf sec'
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
                    varint_bytes32 copy_len sn)
                  (addr_bytes @ [ucast (mode_t_C.arg_C m)])) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C
      (single_copy_opcode' copy_len (mode_t_C.mode_C m)) = 1"
    using single_copy_opcode'_large[OF sz_large] by auto
  note gets_the_best_mode'_result[runs_to_vcg]
  show ?thesis
    unfolding emit_copy'_def
    using bm op
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: bm op)
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_heap_bytes_append_next_typing_preserves2_near_ptr])
           apply (rule inst_byte_fits)
          apply (rule inst_byte_ptr)
         apply (rule inst_byte_dist)
        apply (rule inst_byte_data_disj)
       apply (rule inst_byte_addr_disj)
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken)
       apply (rule write_varint'_success_heap_bytes_append_wordpos_preserves2_near_ptr
        [where n = sn])
              subgoal for t
                using size varint_size'_state_independent[of copy_len t s] by simp
             apply (rule inst_varint_fits)
            apply (intro allI impI)
            subgoal premises prems for t j
            proof -
              have ptr:
                "ptr_valid (heap_typing s)
                  (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
                using inst_varint_valid prems by auto
              show ?thesis
                using ptr prems by simp
            qed
           apply (rule inst_varint_inj)
          apply (rule inst_varint_prefix_disj)
         apply (rule inst_varint_no_overflow)
        apply (rule inst_varint_data_disj)
       apply (rule inst_varint_addr_disj)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF emit_address'_success_byte_heap_bytes_append_preserves2_near_ptr])
          apply (rule mode_ge)
         apply (rule addr_byte_fits)
        apply (simp add: addr_byte_ptr)
       apply (rule addr_byte_dist)
      apply (rule addr_byte_data_disj)
     apply (rule addr_byte_inst_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF cache_update'_preserves_heap_bytes3
       [of _ _ data "unat (sections_t_C.data_pos_C sec)"
          inst "unat (sections_t_C.inst_pos_C sec + 1 + sn)"
          addr_buf "unat (sections_t_C.addr_pos_C sec + 1)"]])
     using near_ptr_lt apply simp
    using emitted
    apply (clarsimp simp: sections_result_def emitted_sections_def sec_ok)
    done
qed

lemma emit_copy'_large_addr_varint_success_emitted_sections:
  assumes emitted:
        "emitted_sections s data inst addr_buf sec data_bytes inst_bytes addr_bytes"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat sn. \<forall>j < unat sn.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat sn < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj:
        "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + sn). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1 + sn)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                emitted_sections t data inst addr_buf sec'
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
                    varint_bytes32 copy_len sn)
                  (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C
      (single_copy_opcode' copy_len (mode_t_C.mode_C m)) = 1"
    using single_copy_opcode'_large[OF sz_large] by auto
  note gets_the_best_mode'_result[runs_to_vcg]
  show ?thesis
    unfolding emit_copy'_def
    using bm op
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: bm op)
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_heap_bytes_append_next_typing_preserves2_near_ptr])
           apply (rule inst_byte_fits)
          apply (rule inst_byte_ptr)
         apply (rule inst_byte_dist)
        apply (rule inst_byte_data_disj)
       apply (rule inst_byte_addr_disj)
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken)
       apply (rule write_varint'_success_heap_bytes_append_wordpos_preserves2_near_ptr
        [where n = sn])
              subgoal for t
                using size varint_size'_state_independent[of copy_len t s] by simp
             apply (rule inst_varint_fits)
            apply (intro allI impI)
            subgoal premises prems for t j
            proof -
              have ptr:
                "ptr_valid (heap_typing s)
                  (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
                using inst_varint_valid prems by auto
              show ?thesis
                using ptr prems by simp
            qed
           apply (rule inst_varint_inj)
          apply (rule inst_varint_prefix_disj)
         apply (rule inst_varint_no_overflow)
        apply (rule inst_varint_data_disj)
       apply (rule inst_varint_addr_disj)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule emit_address'_success_varint_heap_bytes_append_preserves2_near_ptr
       [where n = an])
             apply (rule mode_lt)
            subgoal for t ta
              using addr_size varint_size'_state_independent
                [of "mode_t_C.arg_C m" ta s] by simp
           apply (rule addr_varint_fits)
          apply (intro allI impI)
          subgoal premises prems for t ta j
          proof -
            have ptr:
              "ptr_valid (heap_typing s)
                (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
              using addr_varint_valid prems by auto
            show ?thesis
              using ptr prems by simp
          qed
         apply (rule addr_varint_inj)
        apply (rule addr_varint_prefix_disj)
       apply (rule addr_varint_no_overflow)
      apply (rule addr_varint_data_disj)
     apply (rule addr_varint_inst_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF cache_update'_preserves_heap_bytes3
       [of _ _ data "unat (sections_t_C.data_pos_C sec)"
          inst "unat (sections_t_C.inst_pos_C sec + 1 + sn)"
          addr_buf "unat (sections_t_C.addr_pos_C sec + an)"]])
     using near_ptr_lt apply simp
    using emitted
    apply (clarsimp simp: sections_result_def emitted_sections_def sec_ok)
    done
qed

lemma emit_copy'_small_addr_byte_success_enc_cache_abs:
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C
      (single_copy_opcode' copy_len (mode_t_C.mode_C m)) = 0"
    using single_copy_opcode'_small[OF sz_ge sz_le] by auto
  note gets_the_best_mode'_result[runs_to_vcg]
  show ?thesis
    unfolding emit_copy'_def
    using bm op
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: bm op)
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_preserves_enc_cache_abs])
         apply (rule abs)
        apply (rule inst_byte_fits)
       apply (rule inst_byte_ptr)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF emit_address'_success_byte_preserves_enc_cache_abs])
        apply assumption
       apply (rule mode_ge)
      apply (rule addr_byte_fits)
     apply (simp add: addr_byte_ptr)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF cache_update'_enc_cache_abs_wf[where buf = inst and n = 0]])
      apply assumption
     apply (rule cache_wf)
    apply clarsimp
    done
qed

lemma emit_copy'_small_addr_byte_success_enc_sections_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and target_room: "length target + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
                  (addr_bytes @ [ucast (mode_t_C.arg_C m)])
                  (copy_loop src_seg target (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?op = "single_copy_opcode' copy_len (mode_t_C.mode_C m)"
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf:
    "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le_nat: "unat (mode_t_C.mode_C m) \<le> 8"
    by (rule enc_mode_arg_wf_mode_le8[OF mode_wf])
  have mode_le_word: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have wf_addr:
    "wf_encoding c_out (unat copy_addr) (length src_seg + length target)
       (unat (mode_t_C.mode_C m)) [ucast (mode_t_C.arg_C m)]"
    using mode_wf mode_ge here_eq by (simp add: enc_mode_arg_wf_def)
  have n_pos: "0 < unat copy_len"
    using sz_ge by (simp add: word_le_nat_alt)
  have n32: "unat copy_len < 2 ^ 32"
    using unat_lt2p[of copy_len] by simp
  have a32: "unat copy_addr < 2 ^ 32"
    using unat_lt2p[of copy_addr] by simp
  have here32: "length src_seg + length target < 2 ^ 32"
    using here_eq unat_lt2p[of here] by simp
  have needs:
    "op_t_C.needs_size_C ?op = 0"
    using single_copy_opcode'_small[OF sz_ge sz_le] by auto
  have inst_bytes_eq:
    "copy_inst_bytes (unat copy_len) (unat (mode_t_C.mode_C m)) =
     [ucast (op_t_C.op_C ?op)]"
  proof -
    have find:
      "find_single_copy_opcode (unat copy_len) (unat (mode_t_C.mode_C m)) =
       (unat (op_t_C.op_C ?op), False)"
      using single_copy_opcode'_find_single_copy_opcode
        [OF mode_le_word, of copy_len] needs
      by simp
    show ?thesis
      using find by (simp add: copy_inst_bytes_def Let_def byte_of_unat_ucast32)
  qed
  have decodes_post:
    "section_decodes src_seg tgt_len
      data_bytes
      (inst_bytes @ [ucast (op_t_C.op_C ?op)])
      (addr_bytes @ [ucast (mode_t_C.arg_C m)])
      (copy_loop src_seg target (unat copy_addr) (unat copy_len))
      (cache_update c_out (unat copy_addr))"
    using section_decodes_append_copy
      [OF enc_sections_invD(2)[OF inv] mode_le_nat n_pos n32 a32 here32
          addr_ok target_room wf_addr]
          inst_bytes_eq
    by simp
  show ?thesis
  apply (rule runs_to_weaken[
    OF emit_copy'_small_addr_byte_success_emitted_sections
      [OF enc_sections_invD(1)[OF inv] bm sz_ge sz_le mode_ge sec_ok
          near_ptr_lt inst_byte_fits inst_byte_ptr inst_byte_dist
          inst_byte_data_disj inst_byte_addr_disj addr_byte_fits
          addr_byte_ptr addr_byte_dist addr_byte_data_disj
          addr_byte_inst_disj]])
  using decodes_post by (auto simp: enc_sections_inv_def)
qed

lemma emit_copy'_small_addr_byte_success_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and target_room: "length target + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
                  (addr_bytes @ [ucast (mode_t_C.arg_C m)])
                  (copy_loop src_seg target (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have sections:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec + 1)
              ENC_OK \<and>
            enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
              data_bytes
              (inst_bytes @
                [ucast (op_t_C.op_C
                  (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
              (addr_bytes @ [ucast (mode_t_C.arg_C m)])
              (copy_loop src_seg target (unat copy_addr) (unat copy_len))
              (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_copy'_small_addr_byte_success_enc_sections_inv
      [OF inv abs cache_wf bm sz_ge sz_le mode_ge here_eq addr_ok
          target_room sec_ok inst_byte_fits inst_byte_ptr inst_byte_dist
          inst_byte_data_disj inst_byte_addr_disj addr_byte_fits
          addr_byte_ptr addr_byte_dist addr_byte_data_disj addr_byte_inst_disj])
  have cache:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
            enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_copy'_small_addr_byte_success_enc_cache_abs
      [OF abs cache_wf bm sz_ge sz_le mode_ge inst_byte_fits
          inst_byte_ptr addr_byte_fits addr_byte_ptr])
  have combined:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec + 1)
              ENC_OK \<and>
            enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
              data_bytes
              (inst_bytes @
                [ucast (op_t_C.op_C
                  (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
              (addr_bytes @ [ucast (mode_t_C.arg_C m)])
              (copy_loop src_seg target (unat copy_addr) (unat copy_len))
              (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
            enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using sections cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma emit_copy'_small_addr_varint_success_enc_cache_abs:
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C
      (single_copy_opcode' copy_len (mode_t_C.mode_C m)) = 0"
    using single_copy_opcode'_small[OF sz_ge sz_le] by auto
  note gets_the_best_mode'_result[runs_to_vcg]
  show ?thesis
    unfolding emit_copy'_def
    using bm op
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: bm op)
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_preserves_enc_cache_abs])
         apply (rule abs)
        apply (rule inst_byte_fits)
       apply (rule inst_byte_ptr)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule emit_address'_success_varint_preserves_enc_cache_abs
        [where n = an])
           apply assumption
         apply (rule mode_lt)
         subgoal for t
           using addr_size
                 varint_size'_state_independent
                   [of "mode_t_C.arg_C m" t s]
           by simp
        apply (rule addr_varint_fits)
       apply (intro allI impI)
       subgoal premises prems for t j
       proof -
         have ptr:
           "ptr_valid (heap_typing s)
             (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
           using addr_varint_valid prems by auto
         show ?thesis
           using ptr prems by simp
       qed
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF cache_update'_enc_cache_abs_wf[where buf = inst and n = 0]])
      apply assumption
     apply (rule cache_wf)
    apply clarsimp
    done
qed

lemma emit_copy'_small_addr_varint_success_enc_sections_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and addr_bytes_eq:
        "varint_bytes32 (mode_t_C.arg_C m) an =
         varint_encode (unat (mode_t_C.arg_C m))"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and target_room: "length target + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
                  (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
                  (copy_loop src_seg target (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?op = "single_copy_opcode' copy_len (mode_t_C.mode_C m)"
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf:
    "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le_nat: "unat (mode_t_C.mode_C m) \<le> 8"
    by (rule enc_mode_arg_wf_mode_le8[OF mode_wf])
  have mode_le_word: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have wf_addr:
    "wf_encoding c_out (unat copy_addr) (length src_seg + length target)
       (unat (mode_t_C.mode_C m)) (varint_bytes32 (mode_t_C.arg_C m) an)"
    using mode_wf mode_lt here_eq addr_bytes_eq
    by (simp add: enc_mode_arg_wf_def)
  have n_pos: "0 < unat copy_len"
    using sz_ge by (simp add: word_le_nat_alt)
  have n32: "unat copy_len < 2 ^ 32"
    using unat_lt2p[of copy_len] by simp
  have a32: "unat copy_addr < 2 ^ 32"
    using unat_lt2p[of copy_addr] by simp
  have here32: "length src_seg + length target < 2 ^ 32"
    using here_eq unat_lt2p[of here] by simp
  have needs:
    "op_t_C.needs_size_C ?op = 0"
    using single_copy_opcode'_small[OF sz_ge sz_le] by auto
  have inst_bytes_eq:
    "copy_inst_bytes (unat copy_len) (unat (mode_t_C.mode_C m)) =
     [ucast (op_t_C.op_C ?op)]"
  proof -
    have find:
      "find_single_copy_opcode (unat copy_len) (unat (mode_t_C.mode_C m)) =
       (unat (op_t_C.op_C ?op), False)"
      using single_copy_opcode'_find_single_copy_opcode
        [OF mode_le_word, of copy_len] needs
      by simp
    show ?thesis
      using find by (simp add: copy_inst_bytes_def Let_def byte_of_unat_ucast32)
  qed
  have decodes_post:
    "section_decodes src_seg tgt_len
      data_bytes
      (inst_bytes @ [ucast (op_t_C.op_C ?op)])
      (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
      (copy_loop src_seg target (unat copy_addr) (unat copy_len))
      (cache_update c_out (unat copy_addr))"
    using section_decodes_append_copy
      [OF enc_sections_invD(2)[OF inv] mode_le_nat n_pos n32 a32 here32
          addr_ok target_room wf_addr]
          inst_bytes_eq
    by simp
  show ?thesis
  apply (rule runs_to_weaken[
    OF emit_copy'_small_addr_varint_success_emitted_sections
      [OF enc_sections_invD(1)[OF inv] bm sz_ge sz_le mode_lt addr_size
          sec_ok near_ptr_lt inst_byte_fits inst_byte_ptr inst_byte_dist
          inst_byte_data_disj inst_byte_addr_disj addr_varint_fits
          addr_varint_valid addr_varint_inj addr_varint_prefix_disj
          addr_varint_no_overflow addr_varint_data_disj
          addr_varint_inst_disj]])
  using decodes_post by (auto simp: enc_sections_inv_def)
qed

lemma emit_copy'_small_addr_varint_success_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and addr_bytes_eq:
        "varint_bytes32 (mode_t_C.arg_C m) an =
         varint_encode (unat (mode_t_C.arg_C m))"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and target_room: "length target + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
                  (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
                  (copy_loop src_seg target (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have sections:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec + an)
              ENC_OK \<and>
            enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
              data_bytes
              (inst_bytes @
                [ucast (op_t_C.op_C
                  (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
              (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
              (copy_loop src_seg target (unat copy_addr) (unat copy_len))
              (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_copy'_small_addr_varint_success_enc_sections_inv
      [OF inv abs cache_wf bm sz_ge sz_le mode_lt addr_size addr_bytes_eq
          here_eq addr_ok target_room sec_ok inst_byte_fits inst_byte_ptr
          inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
          addr_varint_fits addr_varint_valid addr_varint_inj
          addr_varint_prefix_disj addr_varint_no_overflow
          addr_varint_data_disj addr_varint_inst_disj])
  have cache:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
            enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_copy'_small_addr_varint_success_enc_cache_abs
      [OF abs cache_wf bm sz_ge sz_le mode_lt addr_size inst_byte_fits
          inst_byte_ptr addr_varint_fits addr_varint_valid])
  have combined:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec + an)
              ENC_OK \<and>
            enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
              data_bytes
              (inst_bytes @
                [ucast (op_t_C.op_C
                  (single_copy_opcode' copy_len (mode_t_C.mode_C m)))])
              (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
              (copy_loop src_seg target (unat copy_addr) (unat copy_len))
              (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
            enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using sections cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma emit_copy'_large_addr_byte_success_enc_cache_abs:
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C
      (single_copy_opcode' copy_len (mode_t_C.mode_C m)) = 1"
    using single_copy_opcode'_large[OF sz_large] by auto
  note gets_the_best_mode'_result[runs_to_vcg]
  show ?thesis
    unfolding emit_copy'_def
    using bm op
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: bm op)
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_preserves_enc_cache_abs])
         apply (rule abs)
        apply (rule inst_byte_fits)
       apply (rule inst_byte_ptr)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_preserves_enc_cache_abs_bounded
        [where n = sn])
         apply assumption
        subgoal for t
          using size varint_size'_state_independent[of copy_len t s] by simp
       apply (rule inst_varint_fits)
      apply (intro allI impI)
      subgoal premises prems for t j
      proof -
        have ptr:
          "ptr_valid (heap_typing s)
            (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
          using inst_varint_valid prems by auto
        show ?thesis
          using ptr prems by simp
      qed
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF emit_address'_success_byte_preserves_enc_cache_abs])
       apply assumption
      apply (rule mode_ge)
     apply (rule addr_byte_fits)
    apply (simp add: addr_byte_ptr)
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF cache_update'_enc_cache_abs_wf[where buf = inst and n = 0]])
      apply assumption
     apply (rule cache_wf)
    apply clarsimp
    done
qed

lemma emit_copy'_large_addr_byte_success_enc_sections_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and copy_len_pos: "0 < unat copy_len"
      and copy_len_bytes_eq:
        "varint_bytes32 copy_len sn = varint_encode (unat copy_len)"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and target_room: "length target + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat sn. \<forall>j < unat sn.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat sn < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + sn).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1 + sn)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
                    varint_bytes32 copy_len sn)
                  (addr_bytes @ [ucast (mode_t_C.arg_C m)])
                  (copy_loop src_seg target (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?op = "single_copy_opcode' copy_len (mode_t_C.mode_C m)"
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf:
    "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le_nat: "unat (mode_t_C.mode_C m) \<le> 8"
    by (rule enc_mode_arg_wf_mode_le8[OF mode_wf])
  have mode_le_word: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have wf_addr:
    "wf_encoding c_out (unat copy_addr) (length src_seg + length target)
       (unat (mode_t_C.mode_C m)) [ucast (mode_t_C.arg_C m)]"
    using mode_wf mode_ge here_eq by (simp add: enc_mode_arg_wf_def)
  have n32: "unat copy_len < 2 ^ 32"
    using unat_lt2p[of copy_len] by simp
  have a32: "unat copy_addr < 2 ^ 32"
    using unat_lt2p[of copy_addr] by simp
  have here32: "length src_seg + length target < 2 ^ 32"
    using here_eq unat_lt2p[of here] by simp
  have needs:
    "op_t_C.needs_size_C ?op = 1"
    using single_copy_opcode'_large[OF sz_large] by auto
  have inst_bytes_eq:
    "copy_inst_bytes (unat copy_len) (unat (mode_t_C.mode_C m)) =
     [ucast (op_t_C.op_C ?op)] @ varint_bytes32 copy_len sn"
  proof -
    have find:
      "find_single_copy_opcode (unat copy_len) (unat (mode_t_C.mode_C m)) =
       (unat (op_t_C.op_C ?op), True)"
      using single_copy_opcode'_find_single_copy_opcode
        [OF mode_le_word, of copy_len] needs
      by simp
    show ?thesis
      using find copy_len_bytes_eq
      by (simp add: copy_inst_bytes_def Let_def byte_of_unat_ucast32)
  qed
  have decodes_post:
    "section_decodes src_seg tgt_len
      data_bytes
      (inst_bytes @ [ucast (op_t_C.op_C ?op)] @ varint_bytes32 copy_len sn)
      (addr_bytes @ [ucast (mode_t_C.arg_C m)])
      (copy_loop src_seg target (unat copy_addr) (unat copy_len))
      (cache_update c_out (unat copy_addr))"
    using section_decodes_append_copy
      [OF enc_sections_invD(2)[OF inv] mode_le_nat copy_len_pos n32 a32 here32
          addr_ok target_room wf_addr]
          inst_bytes_eq
    by simp
  show ?thesis
  apply (rule runs_to_weaken[
    OF emit_copy'_large_addr_byte_success_emitted_sections
      [OF enc_sections_invD(1)[OF inv] bm sz_large size mode_ge sec_ok
          near_ptr_lt inst_byte_fits inst_byte_ptr inst_byte_dist
          inst_byte_data_disj inst_byte_addr_disj inst_varint_fits
          inst_varint_valid inst_varint_inj inst_varint_prefix_disj
          inst_varint_no_overflow inst_varint_data_disj inst_varint_addr_disj
          addr_byte_fits addr_byte_ptr addr_byte_dist addr_byte_data_disj
          addr_byte_inst_disj]])
  using decodes_post by (auto simp: enc_sections_inv_def)
qed

lemma emit_copy'_large_addr_byte_success_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and copy_len_pos: "0 < unat copy_len"
      and copy_len_bytes_eq:
        "varint_bytes32 copy_len sn = varint_encode (unat copy_len)"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and target_room: "length target + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat sn. \<forall>j < unat sn.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat sn < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + sn).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1 + sn)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
                    varint_bytes32 copy_len sn)
                  (addr_bytes @ [ucast (mode_t_C.arg_C m)])
                  (copy_loop src_seg target (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have sections:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec)
              (sections_t_C.inst_pos_C sec + 1 + sn)
              (sections_t_C.addr_pos_C sec + 1)
              ENC_OK \<and>
            enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
              data_bytes
              (inst_bytes @
                [ucast (op_t_C.op_C
                  (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
                varint_bytes32 copy_len sn)
              (addr_bytes @ [ucast (mode_t_C.arg_C m)])
              (copy_loop src_seg target (unat copy_addr) (unat copy_len))
              (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_copy'_large_addr_byte_success_enc_sections_inv
      [OF inv abs cache_wf bm sz_large size copy_len_pos
          copy_len_bytes_eq mode_ge here_eq addr_ok target_room sec_ok
          inst_byte_fits inst_byte_ptr inst_byte_dist inst_byte_data_disj
          inst_byte_addr_disj inst_varint_fits inst_varint_valid
          inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
          inst_varint_data_disj inst_varint_addr_disj addr_byte_fits
          addr_byte_ptr addr_byte_dist addr_byte_data_disj
          addr_byte_inst_disj])
  have cache:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
            enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_copy'_large_addr_byte_success_enc_cache_abs
      [OF abs cache_wf bm sz_large size mode_ge inst_byte_fits
          inst_byte_ptr inst_varint_fits inst_varint_valid
          addr_byte_fits addr_byte_ptr])
  have combined:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec)
              (sections_t_C.inst_pos_C sec + 1 + sn)
              (sections_t_C.addr_pos_C sec + 1)
              ENC_OK \<and>
            enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
              data_bytes
              (inst_bytes @
                [ucast (op_t_C.op_C
                  (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
                varint_bytes32 copy_len sn)
              (addr_bytes @ [ucast (mode_t_C.arg_C m)])
              (copy_loop src_seg target (unat copy_addr) (unat copy_len))
              (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'.
            r = Result sec' \<and>
            enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
            enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
          heap_typing t = heap_typing s) \<rbrace>"
    using sections cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma emit_copy'_large_addr_varint_success_enc_cache_abs:
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op:
    "op_t_C.needs_size_C
      (single_copy_opcode' copy_len (mode_t_C.mode_C m)) = 1"
    using single_copy_opcode'_large[OF sz_large] by auto
  note gets_the_best_mode'_result[runs_to_vcg]
  show ?thesis
    unfolding emit_copy'_def
    using bm op
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: bm op)
    apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF write_byte'_success_preserves_enc_cache_abs])
         apply (rule abs)
        apply (rule inst_byte_fits)
       apply (rule inst_byte_ptr)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule write_varint'_success_preserves_enc_cache_abs_bounded
        [where n = sn])
         apply assumption
        subgoal for t
          using size varint_size'_state_independent[of copy_len t s] by simp
       apply (rule inst_varint_fits)
      apply (intro allI impI)
      subgoal premises prems for t j
      proof -
        have ptr:
          "ptr_valid (heap_typing s)
            (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
          using inst_varint_valid prems by auto
        show ?thesis
          using ptr prems by simp
      qed
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken)
     apply (rule emit_address'_success_varint_preserves_enc_cache_abs
       [where n = an])
         apply assumption
        apply (rule mode_lt)
       subgoal for t ta
         using addr_size
               varint_size'_state_independent
                 [of "mode_t_C.arg_C m" ta s]
         by simp
      apply (rule addr_varint_fits)
     apply (intro allI impI)
     subgoal premises prems for t ta j
     proof -
       have ptr:
         "ptr_valid (heap_typing s)
           (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
         using addr_varint_valid prems by auto
       show ?thesis
         using ptr prems by simp
     qed
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF cache_update'_enc_cache_abs_wf[where buf = inst and n = 0]])
      apply assumption
     apply (rule cache_wf)
    apply clarsimp
    done
qed

lemma emit_copy'_large_addr_varint_success_enc_sections_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and copy_len_pos: "0 < unat copy_len"
      and copy_len_bytes_eq:
        "varint_bytes32 copy_len sn = varint_encode (unat copy_len)"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and addr_bytes_eq:
        "varint_bytes32 (mode_t_C.arg_C m) an =
         varint_encode (unat (mode_t_C.arg_C m))"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and target_room: "length target + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat sn. \<forall>j < unat sn.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat sn < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj:
        "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + sn). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1 + sn)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
                    varint_bytes32 copy_len sn)
                  (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
                  (copy_loop src_seg target (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?op = "single_copy_opcode' copy_len (mode_t_C.mode_C m)"
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf:
    "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le_nat: "unat (mode_t_C.mode_C m) \<le> 8"
    by (rule enc_mode_arg_wf_mode_le8[OF mode_wf])
  have mode_le_word: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have wf_addr:
    "wf_encoding c_out (unat copy_addr) (length src_seg + length target)
       (unat (mode_t_C.mode_C m)) (varint_bytes32 (mode_t_C.arg_C m) an)"
    using mode_wf mode_lt here_eq addr_bytes_eq
    by (simp add: enc_mode_arg_wf_def)
  have n32: "unat copy_len < 2 ^ 32"
    using unat_lt2p[of copy_len] by simp
  have a32: "unat copy_addr < 2 ^ 32"
    using unat_lt2p[of copy_addr] by simp
  have here32: "length src_seg + length target < 2 ^ 32"
    using here_eq unat_lt2p[of here] by simp
  have needs:
    "op_t_C.needs_size_C ?op = 1"
    using single_copy_opcode'_large[OF sz_large] by auto
  have inst_bytes_eq:
    "copy_inst_bytes (unat copy_len) (unat (mode_t_C.mode_C m)) =
     [ucast (op_t_C.op_C ?op)] @ varint_bytes32 copy_len sn"
  proof -
    have find:
      "find_single_copy_opcode (unat copy_len) (unat (mode_t_C.mode_C m)) =
       (unat (op_t_C.op_C ?op), True)"
      using single_copy_opcode'_find_single_copy_opcode
        [OF mode_le_word, of copy_len] needs
      by simp
    show ?thesis
      using find copy_len_bytes_eq
      by (simp add: copy_inst_bytes_def Let_def byte_of_unat_ucast32)
  qed
  have decodes_post:
    "section_decodes src_seg tgt_len
      data_bytes
      (inst_bytes @ [ucast (op_t_C.op_C ?op)] @ varint_bytes32 copy_len sn)
      (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
      (copy_loop src_seg target (unat copy_addr) (unat copy_len))
      (cache_update c_out (unat copy_addr))"
    using section_decodes_append_copy
      [OF enc_sections_invD(2)[OF inv] mode_le_nat copy_len_pos n32 a32 here32
          addr_ok target_room wf_addr]
          inst_bytes_eq
    by simp
  show ?thesis
  apply (rule runs_to_weaken[
    OF emit_copy'_large_addr_varint_success_emitted_sections
      [OF enc_sections_invD(1)[OF inv] bm sz_large size mode_lt addr_size
          sec_ok near_ptr_lt inst_byte_fits inst_byte_ptr inst_byte_dist
          inst_byte_data_disj inst_byte_addr_disj inst_varint_fits
          inst_varint_valid inst_varint_inj inst_varint_prefix_disj
          inst_varint_no_overflow inst_varint_data_disj inst_varint_addr_disj
          addr_varint_fits addr_varint_valid addr_varint_inj
          addr_varint_prefix_disj addr_varint_no_overflow
          addr_varint_data_disj addr_varint_inst_disj]])
  using decodes_post by (auto simp: enc_sections_inv_def)
qed

lemma emit_copy'_large_addr_varint_success_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and copy_len_pos: "0 < unat copy_len"
      and copy_len_bytes_eq:
        "varint_bytes32 copy_len sn = varint_encode (unat copy_len)"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and addr_bytes_eq:
        "varint_bytes32 (mode_t_C.arg_C m) an =
         varint_encode (unat (mode_t_C.arg_C m))"
      and here_eq: "unat here = length src_seg + length target"
      and addr_ok: "unat copy_addr < length src_seg + length target"
      and target_room: "length target + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat sn. \<forall>j < unat sn.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat sn < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj:
        "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + sn). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1 + sn)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
                  data_bytes
                  (inst_bytes @
                    [ucast (op_t_C.op_C
                      (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
                    varint_bytes32 copy_len sn)
                  (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
                  (copy_loop src_seg target (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?section_post =
    "\<lambda>r t.
      (\<exists>sec'.
        r = Result sec' \<and>
        sections_result sec'
          (sections_t_C.data_pos_C sec)
          (sections_t_C.inst_pos_C sec + 1 + sn)
          (sections_t_C.addr_pos_C sec + an)
          ENC_OK \<and>
        enc_sections_inv t data inst addr_buf sec' src_seg tgt_len
          data_bytes
          (inst_bytes @
            [ucast (op_t_C.op_C
              (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
            varint_bytes32 copy_len sn)
          (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
          (copy_loop src_seg target (unat copy_addr) (unat copy_len))
          (cache_update c_out (unat copy_addr))) \<and>
      heap_typing t = heap_typing s"
  let ?cache_post =
    "\<lambda>r t.
      (\<exists>sec'.
        r = Result sec' \<and>
        enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
        enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
      heap_typing t = heap_typing s"
  have sections:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> ?section_post \<rbrace>"
    by (rule emit_copy'_large_addr_varint_success_enc_sections_inv
      [OF inv abs cache_wf bm sz_large size copy_len_pos
          copy_len_bytes_eq mode_lt addr_size addr_bytes_eq here_eq
          addr_ok target_room sec_ok inst_byte_fits inst_byte_ptr
          inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
          inst_varint_fits inst_varint_valid inst_varint_inj
          inst_varint_prefix_disj inst_varint_no_overflow
          inst_varint_data_disj inst_varint_addr_disj addr_varint_fits
          addr_varint_valid addr_varint_inj addr_varint_prefix_disj
          addr_varint_no_overflow addr_varint_data_disj
          addr_varint_inst_disj])
  have cache:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> ?cache_post \<rbrace>"
    by (rule emit_copy'_large_addr_varint_success_enc_cache_abs
      [OF abs cache_wf bm sz_large size mode_lt addr_size
          inst_byte_fits inst_byte_ptr inst_varint_fits inst_varint_valid
          addr_varint_fits addr_varint_valid])
  have combined:
    "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
       \<lbrace> \<lambda>r t. ?section_post r t \<and> ?cache_post r t \<rbrace>"
    using sections cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma emit_copy'_small_addr_byte_success_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_choice:
        "encode_address (enc_cache spec_st) (unat copy_addr)
           (src_len + enc_flushed spec_st) =
         (unat (mode_t_C.mode_C m), [ucast (mode_t_C.arg_C m)],
          cache_update (enc_cache spec_st) (unat copy_addr))"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                enc_sections_state_rel t data inst addr_buf sec'
                  (emit_copy_spec src_len (unat copy_addr)
                    (unat copy_len) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf: "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have pure_sections:
    "enc_data
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_data spec_st"
    "enc_inst
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_inst spec_st @
       [ucast (op_t_C.op_C
         (single_copy_opcode' copy_len (mode_t_C.mode_C m)))]"
    "enc_addr
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_addr spec_st @ [ucast (mode_t_C.arg_C m)]"
    using emit_copy_spec_small_sections
      [OF sz_ge sz_le mode_le addr_choice]
    by simp_all
  show ?thesis
    apply (rule runs_to_weaken[
      OF emit_copy'_small_addr_byte_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] bm sz_ge sz_le mode_ge
            sec_ok near_ptr_lt inst_byte_fits inst_byte_ptr
            inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
            addr_byte_fits addr_byte_ptr addr_byte_dist
            addr_byte_data_disj addr_byte_inst_disj]])
    using pure_sections
    by (auto simp: enc_sections_state_rel_def)
qed

lemma emit_copy'_small_addr_varint_success_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_ge: "(4 :: 32 word) \<le> copy_len"
      and sz_le: "copy_len \<le> (18 :: 32 word)"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and addr_choice:
        "encode_address (enc_cache spec_st) (unat copy_addr)
           (src_len + enc_flushed spec_st) =
         (unat (mode_t_C.mode_C m),
          varint_bytes32 (mode_t_C.arg_C m) an,
          cache_update (enc_cache spec_st) (unat copy_addr))"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                enc_sections_state_rel t data inst addr_buf sec'
                  (emit_copy_spec src_len (unat copy_addr)
                    (unat copy_len) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf: "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have pure_sections:
    "enc_data
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_data spec_st"
    "enc_inst
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_inst spec_st @
       [ucast (op_t_C.op_C
         (single_copy_opcode' copy_len (mode_t_C.mode_C m)))]"
    "enc_addr
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_addr spec_st @ varint_bytes32 (mode_t_C.arg_C m) an"
    using emit_copy_spec_small_sections
      [OF sz_ge sz_le mode_le addr_choice]
    by simp_all
  show ?thesis
    apply (rule runs_to_weaken[
      OF emit_copy'_small_addr_varint_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] bm sz_ge sz_le mode_lt
            addr_size sec_ok near_ptr_lt inst_byte_fits inst_byte_ptr
            inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
            addr_varint_fits addr_varint_valid addr_varint_inj
            addr_varint_prefix_disj addr_varint_no_overflow
            addr_varint_data_disj addr_varint_inst_disj]])
    using pure_sections
    by (auto simp: enc_sections_state_rel_def)
qed

lemma emit_copy'_large_addr_byte_success_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_choice:
        "encode_address (enc_cache spec_st) (unat copy_addr)
           (src_len + enc_flushed spec_st) =
         (unat (mode_t_C.mode_C m), [ucast (mode_t_C.arg_C m)],
          cache_update (enc_cache spec_st) (unat copy_addr))"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat sn. \<forall>j < unat sn.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat sn < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + sn).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1 + sn)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                enc_sections_state_rel t data inst addr_buf sec'
                  (emit_copy_spec src_len (unat copy_addr)
                    (unat copy_len) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf: "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have pure_sections:
    "enc_data
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_data spec_st"
    "enc_inst
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_inst spec_st @
       [ucast (op_t_C.op_C
         (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
       varint_bytes32 copy_len sn"
    "enc_addr
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_addr spec_st @ [ucast (mode_t_C.arg_C m)]"
    using emit_copy_spec_large_sections
      [OF sz_large mode_le size addr_choice]
    by simp_all
  show ?thesis
    apply (rule runs_to_weaken[
      OF emit_copy'_large_addr_byte_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] bm sz_large size mode_ge
            sec_ok near_ptr_lt inst_byte_fits inst_byte_ptr
            inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
            inst_varint_fits inst_varint_valid inst_varint_inj
            inst_varint_prefix_disj inst_varint_no_overflow
            inst_varint_data_disj inst_varint_addr_disj
            addr_byte_fits addr_byte_ptr addr_byte_dist
            addr_byte_data_disj addr_byte_inst_disj]])
    using pure_sections
    by (auto simp: enc_sections_state_rel_def)
qed

lemma emit_copy'_large_addr_varint_success_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and sz_large:
        "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      and size: "varint_size' copy_len s = Some sn"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and addr_choice:
        "encode_address (enc_cache spec_st) (unat copy_addr)
           (src_len + enc_flushed spec_st) =
         (unat (mode_t_C.mode_C m),
          varint_bytes32 (mode_t_C.arg_C m) an,
          cache_update (enc_cache spec_st) (unat copy_addr))"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < sn"
      and inst_varint_valid: "\<forall>j < unat sn.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat sn. \<forall>j < unat sn.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat sn < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < sn \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj:
        "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1 + sn). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec)
                  (sections_t_C.inst_pos_C sec + 1 + sn)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                enc_sections_state_rel t data inst addr_buf sec'
                  (emit_copy_spec src_len (unat copy_addr)
                    (unat copy_len) spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf: "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have pure_sections:
    "enc_data
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_data spec_st"
    "enc_inst
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_inst spec_st @
       [ucast (op_t_C.op_C
         (single_copy_opcode' copy_len (mode_t_C.mode_C m)))] @
       varint_bytes32 copy_len sn"
    "enc_addr
       (emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st) =
     enc_addr spec_st @ varint_bytes32 (mode_t_C.arg_C m) an"
    using emit_copy_spec_large_sections
      [OF sz_large mode_le size addr_choice]
    by simp_all
  show ?thesis
    apply (rule runs_to_weaken[
      OF emit_copy'_large_addr_varint_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] bm sz_large size mode_lt
            addr_size sec_ok near_ptr_lt inst_byte_fits inst_byte_ptr
            inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
            inst_varint_fits inst_varint_valid inst_varint_inj
            inst_varint_prefix_disj inst_varint_no_overflow
            inst_varint_data_disj inst_varint_addr_disj
            addr_varint_fits addr_varint_valid addr_varint_inj
            addr_varint_prefix_disj addr_varint_no_overflow
            addr_varint_data_disj addr_varint_inst_disj]])
    using pure_sections
    by (auto simp: enc_sections_state_rel_def)
qed

lemma flush_pending'_len_zero_noop:
  shows "flush_pending' sec data data_cap inst inst_cap pending 0 \<bullet> s
           \<lbrace> \<lambda>r t. r = Result sec \<and> t = s \<rbrace>"
  unfolding flush_pending'_def
  apply runs_to_vcg
  apply (rule runs_to_whileLoop_exn'[
    where R = "measure (\<lambda>((x :: 32 word \<times> 32 word \<times> sections_t_C), _). 0)"
      and I = "\<lambda>r t. r = Result (0, 0, sec) \<and> t = s"])
     apply simp
    apply simp
   apply simp
  apply runs_to_vcg
  by (auto simp: word_less_nat_alt)

lemma flush_pending'_len_zero_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
  shows "flush_pending' sec data data_cap inst inst_cap pending 0 \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  data_bytes inst_bytes addr_bytes target c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[OF flush_pending'_len_zero_noop])
  using inv abs cache_wf by auto

lemma flush_pending'_len_zero_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_empty: "enc_pending spec_st = []"
  shows "flush_pending' sec data data_cap inst inst_cap pending 0 \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) = enc_data spec_st"
    "enc_inst (flush_pending_spec src_len spec_st) = enc_inst spec_st"
    "enc_addr (flush_pending_spec src_len spec_st) = enc_addr spec_st"
    using flush_pending_spec_empty_sections[OF pending_empty]
    by simp_all
  show ?thesis
    apply (rule runs_to_weaken[OF flush_pending'_len_zero_noop])
    using rel pure_sections
    by (auto simp: enc_sections_state_rel_def)
qed

lemma flush_pending'_len_zero_enc_sections_state_rel_loop_spec:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st =
         heap_bytes_word s pending 0 (0 :: 32 word)"
  shows "flush_pending' sec data data_cap inst inst_cap pending 0 \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_loop_spec src_len
                    (heap_bytes_word s pending 0 (0 :: 32 word)) 0 0
                    spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have pending_empty: "enc_pending spec_st = []"
    using pending_eq by (simp add: heap_bytes_word_def)
  have loop_eq:
    "flush_pending_loop_spec src_len
       (heap_bytes_word s pending 0 (0 :: 32 word)) 0 0 spec_st =
     flush_pending_spec src_len spec_st"
    by (rule flush_pending_loop_spec_eq_flush_pending_spec[OF pending_eq])
  show ?thesis
    apply (rule runs_to_weaken[
      OF flush_pending'_len_zero_enc_sections_state_rel[
        OF rel pending_empty]])
    using loop_eq by auto
qed

lemma runs_to_liftE_bind_throw_result:
  assumes f: "f \<bullet> s \<lbrace>\<lambda>Res v t. P v t\<rbrace>"
  shows "(liftE f >>= throw) \<bullet> s
           \<lbrace>\<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> Q v t) \<and>
                   (\<forall>v. r = Exn v \<longrightarrow> P v t)\<rbrace>"
  apply runs_to_vcg
  apply (rule runs_to_weaken[OF f])
  by auto

lemma flush_pending'_len_one_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and target_room:
        "length target + unat (1 :: 32 word) \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "pending +\<^sub>p uint (0 :: 32 word) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (1 :: 32 word)"
      and data_valid:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and pending_valid:
        "ptr_valid (heap_typing s) (pending +\<^sub>p uint (0 :: 32 word))"
      and data_pending_disj:
        "data +\<^sub>p uint (sections_t_C.data_pos_C sec) \<noteq>
          pending +\<^sub>p uint (0 :: 32 word)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec).
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + 1 < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1).
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec).
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (1 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending 0 (1 :: 32 word))
                  (inst_bytes @ [ucast (1 + (1 :: 32 word))])
                  addr_bytes
                  (target @ heap_bytes_word s pending 0 (1 :: 32 word))
                  c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  unfolding flush_pending'_def
  apply runs_to_vcg
  apply (rule runs_to_whileLoop_exn'[
    where R = "measure
      (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
        if i = 0 then 1 else 0)"
      and I = "\<lambda>r t.
        (r = Result (0, 0, sec) \<or> r = Result (0, 1, sec)) \<and> t = s"])
     apply (clarsimp split: prod.splits)
   apply runs_to_vcg
   using pending_valid apply simp
   apply (subst whileLoop_unroll)
   apply runs_to_vcg
   apply (auto simp: word_less_nat_alt word_le_nat_alt)
  apply (rule runs_to_liftE_bind_throw_result)
  apply (rule runs_to_weaken)
   apply (rule emit_add'_small_success_enc_sections_cache_inv)
                       apply (rule inv)
                      apply (rule abs)
                     apply (rule cache_wf)
                    apply simp
                   apply simp
                  apply (rule target_room)
                 apply (rule sec_ok)
                apply (rule inst_byte_fits)
               apply (rule inst_byte_ptr)
              apply (rule inst_byte_dist)
             apply (rule inst_byte_data_disj)
            apply (rule inst_byte_addr_disj)
           using inst_byte_pending_disj apply simp
          apply (rule data_fits)
         using data_valid apply simp
        using pending_valid apply simp
       using data_pending_disj apply simp
      apply simp
     using data_prefix_disj apply simp
    using data_no_overflow apply simp
   using data_inst_disj apply simp
  using data_addr_disj apply simp
  by auto

lemma flush_pending'_len_one_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 (1 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "pending +\<^sub>p uint (0 :: 32 word) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (1 :: 32 word)"
      and data_valid:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and pending_valid:
        "ptr_valid (heap_typing s) (pending +\<^sub>p uint (0 :: 32 word))"
      and data_pending_disj:
        "data +\<^sub>p uint (sections_t_C.data_pos_C sec) \<noteq>
          pending +\<^sub>p uint (0 :: 32 word)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec).
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + 1 < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1).
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec).
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (1 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have pending_word_len:
    "length (heap_bytes_word s pending 0 (1 :: 32 word)) = 1"
    by simp
  have pending_nonempty: "enc_pending spec_st \<noteq> []"
    using pending_eq pending_word_len by (metis length_0_conv one_neq_zero)
  have pending_short: "length (enc_pending spec_st) < min_run"
    using pending_eq by (simp add: min_run_def)
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (1 :: 32 word))) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (1 :: 32 word))) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (1 :: 32 word))) spec_st)"
    using flush_pending_spec_short_nonempty_sections
      [OF pending_nonempty pending_short] pending_eq
    by (simp_all add: emit_inst_spec_def encode_one.simps
                      find_single_add_opcode_def)
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or> r = Result (0, 1, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply simp
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_state_rel[
        where src_len = src_len])
                       apply (rule rel)
                      apply simp
                     apply simp
                    apply (rule sec_ok)
                   apply (rule inst_byte_fits)
                  apply (rule inst_byte_ptr)
                 apply (rule inst_byte_dist)
                apply (rule inst_byte_data_disj)
               apply (rule inst_byte_addr_disj)
              using inst_byte_pending_disj apply simp
             apply (rule data_fits)
            using data_valid apply simp
           using pending_valid apply simp
          using data_pending_disj apply simp
         apply simp
        using data_prefix_disj apply simp
       using data_no_overflow apply simp
      using data_inst_disj apply simp
     using data_addr_disj apply simp
    using pure_sections by (auto simp: enc_sections_state_rel_def)
qed

lemma flush_pending'_len_two_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and target_room:
        "length target + unat (2 :: 32 word) \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (2 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (2 :: 32 word)"
      and data_valid: "\<forall>j < unat (2 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat (2 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (2 :: 32 word).
        \<forall>j < unat (2 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (2 :: 32 word).
        \<forall>j < unat (2 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (2 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (2 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (2 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (2 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (2 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending 0 (2 :: 32 word))
                  (inst_bytes @ [ucast (1 + (2 :: 32 word))])
                  addr_bytes
                  (target @ heap_bytes_word s pending 0 (2 :: 32 word))
                  c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  unfolding flush_pending'_def
  apply runs_to_vcg
  apply (rule runs_to_whileLoop_exn'[
    where R = "measure
      (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
        if i = 0 then 2 else if i = 1 then 1 else 0)"
      and I = "\<lambda>r t.
        (r = Result (0, 0, sec) \<or>
         r = Result (0, 1, sec) \<or>
         r = Result (0, 2, sec)) \<and> t = s"])
     apply (clarsimp split: prod.splits)
   apply runs_to_vcg
   using pending_valid apply (simp add: word_less_nat_alt)
   apply (subst whileLoop_unroll)
   apply runs_to_vcg
   apply (subst whileLoop_unroll)
   apply runs_to_vcg
   subgoal
     apply runs_to_vcg
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt)
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=0 in allE)
          apply simp
         apply (erule_tac x=1 in allE)
         apply simp
       apply simp
      apply (subst whileLoop_unroll)
      apply runs_to_vcg
     done
    subgoal
     apply runs_to_vcg
     apply (erule_tac x=1 in allE)
     apply simp
     done
    done
  apply (auto simp: word_less_nat_alt word_le_nat_alt)
  apply (rule runs_to_liftE_bind_throw_result)
  apply (rule runs_to_weaken)
   apply (rule emit_add'_small_success_enc_sections_cache_inv)
                       apply (rule inv)
                      apply (rule abs)
                     apply (rule cache_wf)
                    apply simp
                   apply simp
                  apply (rule target_room)
                 apply (rule sec_ok)
                apply (rule inst_byte_fits)
               apply (rule inst_byte_ptr)
              apply (rule inst_byte_dist)
             apply (rule inst_byte_data_disj)
            apply (rule inst_byte_addr_disj)
           using inst_byte_pending_disj apply simp
          apply (rule data_fits)
         using data_valid apply simp
        using pending_valid apply simp
       using data_pending_disj apply simp
      using data_inj apply simp
     using data_prefix_disj apply simp
    apply (rule data_no_overflow)
   using data_inst_disj apply simp
  using data_addr_disj apply simp
  by auto

lemma flush_pending'_len_two_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 (2 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (2 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (2 :: 32 word)"
      and data_valid: "\<forall>j < unat (2 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat (2 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (2 :: 32 word).
        \<forall>j < unat (2 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (2 :: 32 word).
        \<forall>j < unat (2 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (2 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (2 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (2 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (2 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (2 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have pending_word_len:
    "length (heap_bytes_word s pending 0 (2 :: 32 word)) = 2"
    by simp
  have pending_nonempty: "enc_pending spec_st \<noteq> []"
    using pending_eq pending_word_len by (metis length_0_conv numeral_2_eq_2 zero_neq_numeral)
  have pending_short: "length (enc_pending spec_st) < min_run"
    using pending_eq by (simp add: min_run_def)
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (2 :: 32 word))) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (2 :: 32 word))) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (2 :: 32 word))) spec_st)"
    using flush_pending_spec_short_nonempty_sections
      [OF pending_nonempty pending_short] pending_eq
    by (simp_all add: emit_inst_spec_def encode_one.simps
                      find_single_add_opcode_def)
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 2 else if i = 1 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or>
           r = Result (0, 1, sec) \<or>
           r = Result (0, 2, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply (simp add: word_less_nat_alt)
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     subgoal
       apply runs_to_vcg
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply runs_to_vcg
            apply (erule_tac x=0 in allE)
            apply simp
           apply (erule_tac x=1 in allE)
           apply simp
         apply simp
        apply (subst whileLoop_unroll)
        apply runs_to_vcg
       done
      subgoal
       apply runs_to_vcg
       apply (erule_tac x=1 in allE)
       apply simp
       done
      done
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_state_rel[
        where src_len = src_len])
                       apply (rule rel)
                      apply simp
                     apply simp
                    apply (rule sec_ok)
                   apply (rule inst_byte_fits)
                  apply (rule inst_byte_ptr)
                 apply (rule inst_byte_dist)
                apply (rule inst_byte_data_disj)
               apply (rule inst_byte_addr_disj)
              using inst_byte_pending_disj apply simp
             apply (rule data_fits)
            using data_valid apply simp
           using pending_valid apply simp
          using data_pending_disj apply simp
         using data_inj apply simp
        using data_prefix_disj apply simp
       apply (rule data_no_overflow)
      using data_inst_disj apply simp
     using data_addr_disj apply simp
    using pure_sections by (auto simp: enc_sections_state_rel_def)
qed

lemma flush_pending'_len_three_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and target_room:
        "length target + unat (3 :: 32 word) \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (3 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (3 :: 32 word)"
      and data_valid: "\<forall>j < unat (3 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat (3 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (3 :: 32 word).
        \<forall>j < unat (3 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (3 :: 32 word).
        \<forall>j < unat (3 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (3 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (3 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (3 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (3 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (3 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending 0 (3 :: 32 word))
                  (inst_bytes @ [ucast (1 + (3 :: 32 word))])
                  addr_bytes
                  (target @ heap_bytes_word s pending 0 (3 :: 32 word))
                  c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  unfolding flush_pending'_def
  apply runs_to_vcg
  apply (rule runs_to_whileLoop_exn'[
    where R = "measure
      (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
        if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else 0)"
      and I = "\<lambda>r t.
        (r = Result (0, 0, sec) \<or>
         r = Result (0, 1, sec) \<or>
         r = Result (0, 2, sec) \<or>
         r = Result (0, 3, sec)) \<and> t = s"])
     apply (clarsimp split: prod.splits)
   apply runs_to_vcg
   using pending_valid apply (simp add: word_less_nat_alt)
   apply (subst whileLoop_unroll)
   apply runs_to_vcg
   apply (subst whileLoop_unroll)
   apply runs_to_vcg
   apply (auto simp: word_less_nat_alt word_le_nat_alt)
   subgoal
     apply runs_to_vcg
        apply (erule_tac x=0 in allE)
        apply simp
       apply (erule_tac x=1 in allE)
       apply simp
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt)
     subgoal
       apply (erule_tac x=2 in allE)
       apply simp
       done
     subgoal
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       done
     subgoal
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       done
     subgoal
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       done
     done
   subgoal
     apply runs_to_vcg
        apply (erule_tac x=1 in allE)
        apply simp
       apply (erule_tac x=2 in allE)
       apply simp
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt)
     subgoal
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       done
     done
   subgoal
     apply runs_to_vcg
     apply (erule_tac x=2 in allE)
     apply simp
     done
  apply (rule runs_to_liftE_bind_throw_result)
  apply (rule runs_to_weaken)
   apply (rule emit_add'_small_success_enc_sections_cache_inv)
                       apply (rule inv)
                      apply (rule abs)
                     apply (rule cache_wf)
                    apply simp
                   apply simp
                  apply (rule target_room)
                 apply (rule sec_ok)
                apply (rule inst_byte_fits)
               apply (rule inst_byte_ptr)
              apply (rule inst_byte_dist)
             apply (rule inst_byte_data_disj)
            apply (rule inst_byte_addr_disj)
           using inst_byte_pending_disj apply simp
          apply (rule data_fits)
         using data_valid apply simp
        using pending_valid apply simp
       using data_pending_disj apply simp
      using data_inj apply simp
     using data_prefix_disj apply simp
    apply (rule data_no_overflow)
   using data_inst_disj apply simp
  using data_addr_disj apply simp
  by auto

lemma flush_pending'_len_three_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 (3 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (3 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (3 :: 32 word)"
      and data_valid: "\<forall>j < unat (3 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat (3 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (3 :: 32 word).
        \<forall>j < unat (3 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (3 :: 32 word).
        \<forall>j < unat (3 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (3 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (3 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (3 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (3 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (3 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have pending_word_len:
    "length (heap_bytes_word s pending 0 (3 :: 32 word)) = 3"
    by simp
  have pending_nonempty: "enc_pending spec_st \<noteq> []"
    using pending_eq pending_word_len by (metis length_0_conv numeral_3_eq_3 zero_neq_numeral)
  have pending_short: "length (enc_pending spec_st) < min_run"
    using pending_eq by (simp add: min_run_def)
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (3 :: 32 word))) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (3 :: 32 word))) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (3 :: 32 word))) spec_st)"
    using flush_pending_spec_short_nonempty_sections
      [OF pending_nonempty pending_short] pending_eq
    by (simp_all add: emit_inst_spec_def encode_one.simps
                      find_single_add_opcode_def)
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or>
           r = Result (0, 1, sec) \<or>
           r = Result (0, 2, sec) \<or>
           r = Result (0, 3, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply (simp add: word_less_nat_alt)
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt)
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=0 in allE)
          apply simp
         apply (erule_tac x=1 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (erule_tac x=2 in allE)
         apply simp
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (auto simp: word_less_nat_alt word_le_nat_alt)
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=1 in allE)
          apply simp
         apply (erule_tac x=2 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
       apply (erule_tac x=2 in allE)
       apply simp
       done
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_state_rel[
        where src_len = src_len])
                       apply (rule rel)
                      apply simp
                     apply simp
                    apply (rule sec_ok)
                   apply (rule inst_byte_fits)
                  apply (rule inst_byte_ptr)
                 apply (rule inst_byte_dist)
                apply (rule inst_byte_data_disj)
               apply (rule inst_byte_addr_disj)
              using inst_byte_pending_disj apply simp
             apply (rule data_fits)
            using data_valid apply simp
           using pending_valid apply simp
          using data_pending_disj apply simp
         using data_inj apply simp
        using data_prefix_disj apply simp
       apply (rule data_no_overflow)
      using data_inst_disj apply simp
     using data_addr_disj apply simp
    using pure_sections by (auto simp: enc_sections_state_rel_def)
qed

lemma flush_pending'_len_four_run_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and pending_all_eq: "\<forall>j < unat (4 :: 32 word).
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' (4 :: 32 word) s = Some n"
      and target_room:
        "length target + unat (4 :: 32 word) \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ [heap_w8 s pending])
                  (inst_bytes @ [0] @ varint_bytes32 (4 :: 32 word) n)
                  addr_bytes
                  (target @ replicate (unat (4 :: 32 word)) (heap_w8 s pending))
                  c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?fill = "heap_w8 s pending"
  have p1:
    "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1)) = ?fill"
    using pending_all_eq[rule_format, of 1] by simp
  have p2:
    "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2)) = ?fill"
    using pending_all_eq[rule_format, of 2] by simp
  have p3:
    "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3)) = ?fill"
    using pending_all_eq[rule_format, of 3] by simp
  have v0:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0))"
    using pending_valid[rule_format, of 0] by simp
  have v1:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
    using pending_valid[rule_format, of 1] by simp
  have v2:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
    using pending_valid[rule_format, of 2] by simp
  have v3:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
    using pending_valid[rule_format, of 3] by simp
  have size_unique:
    "\<And>n'. varint_size' (4 :: 32 word) s = Some n' \<Longrightarrow> n' = n"
    using size by simp
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    using pending_valid apply (simp add: word_less_nat_alt)
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
     apply (erule_tac x=1 in allE)
     apply (simp add: pending_all_eq)
    using p1 apply simp
    using pending_valid p1 p2 p3
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    using v0 v1 v2 v3
    apply simp_all
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
     apply (erule_tac x=2 in allE)
     apply (simp add: pending_all_eq)
    using p2 apply simp
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    using p3 v0 v1 v2 v3
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply (rule runs_to_weaken)
     apply (rule emit_run'_success_enc_sections_cache_inv)
                          apply (rule inv)
                         apply (rule abs)
                        apply (rule cache_wf)
                       apply (rule size)
                      apply simp
                     apply (rule target_room)
                    apply (rule sec_ok)
                   apply (rule inst_byte_fits)
                  apply (rule inst_byte_ptr)
                 apply (rule inst_byte_dist)
                apply (rule inst_byte_data_disj)
               apply (rule inst_byte_addr_disj)
              using size_unique inst_varint_fits apply blast
             using size_unique inst_varint_valid apply blast
            using size_unique inst_varint_inj apply blast
           using size_unique inst_varint_prefix_disj apply blast
          using size_unique inst_varint_no_overflow apply blast
         using size_unique inst_varint_data_disj apply blast
        using size_unique inst_varint_addr_disj apply blast
       apply (rule data_byte_fits)
      apply (rule data_byte_ptr)
     apply (rule data_byte_dist)
    using size_unique data_byte_inst_disj apply blast
   apply (rule data_byte_addr_disj)
    apply clarsimp
    apply runs_to_vcg
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    done
qed

lemma flush_pending'_len_four_run_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 (4 :: 32 word)"
      and pending_all_eq: "\<forall>j < unat (4 :: 32 word).
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' (4 :: 32 word) s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?fill = "heap_w8 s pending"
  have unat4[simp]: "unat (4 :: 32 word) = 4"
    by simp
  have p0:
    "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0)) = ?fill"
    using pending_all_eq[rule_format, of 0] by simp
  have p1:
    "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1)) = ?fill"
    using pending_all_eq[rule_format, of 1] by simp
  have p2:
    "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2)) = ?fill"
    using pending_all_eq[rule_format, of 2] by simp
  have p3:
    "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3)) = ?fill"
    using pending_all_eq[rule_format, of 3] by simp
  have v0:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0))"
    using pending_valid[rule_format, of 0] by simp
  have v1:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
    using pending_valid[rule_format, of 1] by simp
  have v2:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
    using pending_valid[rule_format, of 2] by simp
  have v3:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
    using pending_valid[rule_format, of 3] by simp
  have bytes_four:
    "heap_bytes_word s pending 0 (4 :: 32 word) =
      [?fill, ?fill, ?fill, ?fill]"
    using p0 p1 p2 p3
    by (simp add: heap_bytes_word_def upt_rec)
  have pending_four:
    "enc_pending spec_st = [?fill, ?fill, ?fill, ?fill]"
    using pending_eq bytes_four by simp
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RRun ?fill (unat (4 :: 32 word))) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RRun ?fill (unat (4 :: 32 word))) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RRun ?fill (unat (4 :: 32 word))) spec_st)"
    using flush_pending_spec_four_run[OF pending_four]
    by simp_all
  have size_unique:
    "\<And>n'. varint_size' (4 :: 32 word) s = Some n' \<Longrightarrow> n' = n"
    using size by simp
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    using pending_valid apply (simp add: word_less_nat_alt)
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
     apply (erule_tac x=1 in allE)
     apply (simp add: pending_all_eq)
    using p1 apply simp
    using pending_valid p1 p2 p3
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    using v0 v1 v2 v3
    apply simp_all
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
     apply (erule_tac x=2 in allE)
     apply (simp add: pending_all_eq)
    using p2 apply simp
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    using p3 v0 v1 v2 v3
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply (rule runs_to_weaken)
     apply (rule emit_pending_run_chunk_enc_sections_state_rel[
        where src_len = src_len])
                     apply (rule rel)
                    apply (rule sec_ok)
                   apply (rule inst_byte_fits)
                  apply (rule inst_byte_ptr)
                 apply (rule inst_byte_dist)
                apply (rule inst_byte_data_disj)
               apply (rule inst_byte_addr_disj)
              using size_unique inst_varint_fits apply blast
             using size_unique inst_varint_valid apply blast
            using size_unique inst_varint_inj apply blast
           using size_unique inst_varint_prefix_disj apply blast
          using size_unique inst_varint_no_overflow apply blast
         using size_unique inst_varint_data_disj apply blast
        using size_unique inst_varint_addr_disj apply blast
       apply (rule data_byte_fits)
      apply (rule data_byte_ptr)
     apply (rule data_byte_dist)
    using size_unique data_byte_inst_disj apply blast
   apply (rule data_byte_addr_disj)
    using pure_sections
    apply (clarsimp simp: enc_sections_state_rel_def sections_result_def)
    apply runs_to_vcg
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    done
qed

lemma flush_pending'_len_four_add_break1_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and pending_break1:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1)) \<noteq>
         heap_w8 s pending"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and target_room:
        "length target + unat (4 :: 32 word) \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (4 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (4 :: 32 word)"
      and data_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (4 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending 0 (4 :: 32 word))
                  (inst_bytes @ [ucast (1 + (4 :: 32 word))])
                  addr_bytes
                  (target @ heap_bytes_word s pending 0 (4 :: 32 word))
                  c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have v0:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0))"
    using pending_valid[rule_format, of 0] by simp
  have v1:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
    using pending_valid[rule_format, of 1] by simp
  have v2:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
    using pending_valid[rule_format, of 2] by simp
  have v3:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
    using pending_valid[rule_format, of 3] by simp
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or>
           r = Result (0, 1, sec) \<or>
           r = Result (0, 2, sec) \<or>
           r = Result (0, 3, sec) \<or>
           r = Result (0, 4, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply (simp add: word_less_nat_alt)
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt pending_break1)
     subgoal
       apply runs_to_vcg
          using v0 apply simp
         using v1 apply simp
       using pending_break1 apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=1 in allE)
          apply simp
         apply (erule_tac x=2 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (erule_tac x=3 in allE)
         apply simp
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (auto simp: word_less_nat_alt word_le_nat_alt)
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=2 in allE)
          apply simp
         apply (erule_tac x=3 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
       apply (erule_tac x=3 in allE)
       apply simp
       done
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_cache_inv)
                         apply (rule inv)
                        apply (rule abs)
                       apply (rule cache_wf)
                      apply simp
                     apply simp
                    apply (rule target_room)
                   apply (rule sec_ok)
                  apply (rule inst_byte_fits)
                 apply (rule inst_byte_ptr)
                apply (rule inst_byte_dist)
               apply (rule inst_byte_data_disj)
              apply (rule inst_byte_addr_disj)
             using inst_byte_pending_disj apply simp
            apply (rule data_fits)
           using data_valid apply simp
          using pending_valid apply simp
         using data_pending_disj apply simp
        using data_inj apply simp
       using data_prefix_disj apply simp
      apply (rule data_no_overflow)
     using data_inst_disj apply simp
    using data_addr_disj apply simp
    by auto
qed

lemma flush_pending'_len_four_add_break1_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 (4 :: 32 word)"
      and pending_break1:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1)) \<noteq>
         heap_w8 s pending"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (4 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (4 :: 32 word)"
      and data_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (4 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?b0 = "heap_w8 s pending"
  let ?b1 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
  let ?b2 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
  let ?b3 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
  have unat4[simp]: "unat (4 :: 32 word) = 4"
    by simp
  have bytes_four:
    "heap_bytes_word s pending 0 (4 :: 32 word) =
      [?b0, ?b1, ?b2, ?b3]"
    by (simp add: heap_bytes_word_def upt_rec)
  have v0:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0))"
    using pending_valid[rule_format, of 0] by simp
  have v1:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
    using pending_valid[rule_format, of 1] by simp
  have v2:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
    using pending_valid[rule_format, of 2] by simp
  have v3:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
    using pending_valid[rule_format, of 3] by simp
  have pending_four:
    "enc_pending spec_st = [?b0, ?b1, ?b2, ?b3]"
    using pending_eq bytes_four by simp
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    using flush_pending_spec_four_add_break1[OF pending_four pending_break1]
          bytes_four
    by simp_all
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or>
           r = Result (0, 1, sec) \<or>
           r = Result (0, 2, sec) \<or>
           r = Result (0, 3, sec) \<or>
           r = Result (0, 4, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply (simp add: word_less_nat_alt)
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt pending_break1)
     subgoal
       apply runs_to_vcg
          using v0 apply simp
         using v1 apply simp
       using pending_break1 apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=1 in allE)
          apply simp
         apply (erule_tac x=2 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (erule_tac x=3 in allE)
         apply simp
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (auto simp: word_less_nat_alt word_le_nat_alt)
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=2 in allE)
          apply simp
         apply (erule_tac x=3 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
       apply (erule_tac x=3 in allE)
       apply simp
       done
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_state_rel[
        where src_len = src_len])
                       apply (rule rel)
                      apply simp
                     apply simp
                    apply (rule sec_ok)
                   apply (rule inst_byte_fits)
                  apply (rule inst_byte_ptr)
                 apply (rule inst_byte_dist)
                apply (rule inst_byte_data_disj)
               apply (rule inst_byte_addr_disj)
              using inst_byte_pending_disj apply simp
             apply (rule data_fits)
            using data_valid apply simp
           using pending_valid apply simp
          using data_pending_disj apply simp
         using data_inj apply simp
        using data_prefix_disj apply simp
       apply (rule data_no_overflow)
      using data_inst_disj apply simp
     using data_addr_disj apply simp
    using pure_sections by (auto simp: enc_sections_state_rel_def)
qed

lemma flush_pending'_len_four_add_break2_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and pending_eq01:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1)) =
         heap_w8 s pending"
      and pending_break2:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2)) \<noteq>
         heap_w8 s pending"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and target_room:
        "length target + unat (4 :: 32 word) \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (4 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (4 :: 32 word)"
      and data_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (4 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending 0 (4 :: 32 word))
                  (inst_bytes @ [ucast (1 + (4 :: 32 word))])
                  addr_bytes
                  (target @ heap_bytes_word s pending 0 (4 :: 32 word))
                  c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have v0:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0))"
    using pending_valid[rule_format, of 0] by simp
  have v1:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
    using pending_valid[rule_format, of 1] by simp
  have v2:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
    using pending_valid[rule_format, of 2] by simp
  have v3:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
    using pending_valid[rule_format, of 3] by simp
  have p1:
    "heap_w8 s (pending +\<^sub>p 1) = heap_w8 s pending"
    using pending_eq01 by simp
  have p2_ne:
    "heap_w8 s (pending +\<^sub>p 2) \<noteq> heap_w8 s pending"
    using pending_break2 by simp
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or>
           r = Result (0, 1, sec) \<or>
           r = Result (0, 2, sec) \<or>
           r = Result (0, 3, sec) \<or>
           r = Result (0, 4, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply (simp add: word_less_nat_alt)
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt pending_eq01 pending_break2)
     subgoal
       apply runs_to_vcg
          using v0 apply simp
         using v1 apply simp
        using pending_eq01 apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using v2 pending_break2 apply (auto simp: word_less_nat_alt word_le_nat_alt)
       using p1 p2_ne apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using p1 p2_ne apply simp
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=1 in allE)
          apply simp
         apply (erule_tac x=2 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (erule_tac x=3 in allE)
         apply simp
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (auto simp: word_less_nat_alt word_le_nat_alt)
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=2 in allE)
          apply simp
         apply (erule_tac x=3 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
       apply (erule_tac x=3 in allE)
       apply simp
       done
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_cache_inv)
                         apply (rule inv)
                        apply (rule abs)
                       apply (rule cache_wf)
                      apply simp
                     apply simp
                    apply (rule target_room)
                   apply (rule sec_ok)
                  apply (rule inst_byte_fits)
                 apply (rule inst_byte_ptr)
                apply (rule inst_byte_dist)
               apply (rule inst_byte_data_disj)
              apply (rule inst_byte_addr_disj)
             using inst_byte_pending_disj apply simp
            apply (rule data_fits)
           using data_valid apply simp
          using pending_valid apply simp
         using data_pending_disj apply simp
        using data_inj apply simp
       using data_prefix_disj apply simp
      apply (rule data_no_overflow)
     using data_inst_disj apply simp
    using data_addr_disj apply simp
    by auto
qed

lemma flush_pending'_len_four_add_break2_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 (4 :: 32 word)"
      and pending_eq01:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1)) =
         heap_w8 s pending"
      and pending_break2:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2)) \<noteq>
         heap_w8 s pending"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (4 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (4 :: 32 word)"
      and data_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (4 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?b0 = "heap_w8 s pending"
  let ?b2 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
  let ?b3 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
  have unat4[simp]: "unat (4 :: 32 word) = 4"
    by simp
  have bytes_four:
    "heap_bytes_word s pending 0 (4 :: 32 word) =
      [?b0, ?b0, ?b2, ?b3]"
    using pending_eq01
    by (simp add: heap_bytes_word_def upt_rec)
  have v0:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0))"
    using pending_valid[rule_format, of 0] by simp
  have v1:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
    using pending_valid[rule_format, of 1] by simp
  have v2:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
    using pending_valid[rule_format, of 2] by simp
  have v3:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
    using pending_valid[rule_format, of 3] by simp
  have p1:
    "heap_w8 s (pending +\<^sub>p 1) = heap_w8 s pending"
    using pending_eq01 by simp
  have p2_ne:
    "heap_w8 s (pending +\<^sub>p 2) \<noteq> heap_w8 s pending"
    using pending_break2 by simp
  have pending_four:
    "enc_pending spec_st = [?b0, ?b0, ?b2, ?b3]"
    using pending_eq bytes_four by simp
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    using flush_pending_spec_four_add_break2[OF pending_four pending_break2]
          bytes_four
    by simp_all
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or>
           r = Result (0, 1, sec) \<or>
           r = Result (0, 2, sec) \<or>
           r = Result (0, 3, sec) \<or>
           r = Result (0, 4, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply (simp add: word_less_nat_alt)
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt pending_eq01 pending_break2)
     subgoal
       apply runs_to_vcg
          using v0 apply simp
         using v1 apply simp
        using pending_eq01 apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using v2 pending_break2 apply (auto simp: word_less_nat_alt word_le_nat_alt)
       using p1 p2_ne apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using p1 p2_ne apply simp
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=1 in allE)
          apply simp
         apply (erule_tac x=2 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (erule_tac x=3 in allE)
         apply simp
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (auto simp: word_less_nat_alt word_le_nat_alt)
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=2 in allE)
          apply simp
         apply (erule_tac x=3 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
       apply (erule_tac x=3 in allE)
       apply simp
       done
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_state_rel[
        where src_len = src_len])
                       apply (rule rel)
                      apply simp
                     apply simp
                    apply (rule sec_ok)
                   apply (rule inst_byte_fits)
                  apply (rule inst_byte_ptr)
                 apply (rule inst_byte_dist)
                apply (rule inst_byte_data_disj)
               apply (rule inst_byte_addr_disj)
              using inst_byte_pending_disj apply simp
             apply (rule data_fits)
            using data_valid apply simp
           using pending_valid apply simp
          using data_pending_disj apply simp
         using data_inj apply simp
        using data_prefix_disj apply simp
       apply (rule data_no_overflow)
      using data_inst_disj apply simp
     using data_addr_disj apply simp
    using pure_sections by (auto simp: enc_sections_state_rel_def)
qed

lemma flush_pending'_len_four_add_break3_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and pending_eq01:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1)) =
         heap_w8 s pending"
      and pending_eq02:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2)) =
         heap_w8 s pending"
      and pending_break3:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3)) \<noteq>
         heap_w8 s pending"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and target_room:
        "length target + unat (4 :: 32 word) \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (4 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (4 :: 32 word)"
      and data_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (4 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_inv t data inst addr sec' src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending 0 (4 :: 32 word))
                  (inst_bytes @ [ucast (1 + (4 :: 32 word))])
                  addr_bytes
                  (target @ heap_bytes_word s pending 0 (4 :: 32 word))
                  c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have v0:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0))"
    using pending_valid[rule_format, of 0] by simp
  have v1:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
    using pending_valid[rule_format, of 1] by simp
  have v2:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
    using pending_valid[rule_format, of 2] by simp
  have v3:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
    using pending_valid[rule_format, of 3] by simp
  have p1:
    "heap_w8 s (pending +\<^sub>p 1) = heap_w8 s pending"
    using pending_eq01 by simp
  have p2:
    "heap_w8 s (pending +\<^sub>p 2) = heap_w8 s pending"
    using pending_eq02 by simp
  have p3_ne:
    "heap_w8 s (pending +\<^sub>p 3) \<noteq> heap_w8 s pending"
    using pending_break3 by simp
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or>
           r = Result (0, 1, sec) \<or>
           r = Result (0, 2, sec) \<or>
           r = Result (0, 3, sec) \<or>
           r = Result (0, 4, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply (simp add: word_less_nat_alt)
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt
                       pending_eq01 pending_eq02 pending_break3)
     subgoal
       apply runs_to_vcg
          using v0 apply simp
         using v1 apply simp
        using p1 apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using v2 p2 apply (auto simp: word_less_nat_alt word_le_nat_alt)
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using v3 p3_ne apply (auto simp: word_less_nat_alt word_le_nat_alt)
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using p3_ne apply simp
       using p1 apply simp
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=1 in allE)
          apply simp
         apply (erule_tac x=2 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (erule_tac x=3 in allE)
         apply simp
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (auto simp: word_less_nat_alt word_le_nat_alt)
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=2 in allE)
          apply simp
         apply (erule_tac x=3 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
       apply (erule_tac x=3 in allE)
       apply simp
       done
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_cache_inv)
                         apply (rule inv)
                        apply (rule abs)
                       apply (rule cache_wf)
                      apply simp
                     apply simp
                    apply (rule target_room)
                   apply (rule sec_ok)
                  apply (rule inst_byte_fits)
                 apply (rule inst_byte_ptr)
                apply (rule inst_byte_dist)
               apply (rule inst_byte_data_disj)
              apply (rule inst_byte_addr_disj)
             using inst_byte_pending_disj apply simp
            apply (rule data_fits)
           using data_valid apply simp
          using pending_valid apply simp
         using data_pending_disj apply simp
        using data_inj apply simp
       using data_prefix_disj apply simp
      apply (rule data_no_overflow)
     using data_inst_disj apply simp
    using data_addr_disj apply simp
    by auto
qed

lemma flush_pending'_len_four_add_break3_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 (4 :: 32 word)"
      and pending_eq01:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1)) =
         heap_w8 s pending"
      and pending_eq02:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2)) =
         heap_w8 s pending"
      and pending_break3:
        "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3)) \<noteq>
         heap_w8 s pending"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (4 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (4 :: 32 word)"
      and data_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (4 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?b0 = "heap_w8 s pending"
  let ?b3 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
  have unat4[simp]: "unat (4 :: 32 word) = 4"
    by simp
  have bytes_four:
    "heap_bytes_word s pending 0 (4 :: 32 word) =
      [?b0, ?b0, ?b0, ?b3]"
    using pending_eq01 pending_eq02
    by (simp add: heap_bytes_word_def upt_rec)
  have v0:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 0))"
    using pending_valid[rule_format, of 0] by simp
  have v1:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
    using pending_valid[rule_format, of 1] by simp
  have v2:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
    using pending_valid[rule_format, of 2] by simp
  have v3:
    "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
    using pending_valid[rule_format, of 3] by simp
  have p1:
    "heap_w8 s (pending +\<^sub>p 1) = heap_w8 s pending"
    using pending_eq01 by simp
  have p2:
    "heap_w8 s (pending +\<^sub>p 2) = heap_w8 s pending"
    using pending_eq02 by simp
  have p3_ne:
    "heap_w8 s (pending +\<^sub>p 3) \<noteq> heap_w8 s pending"
    using pending_break3 by simp
  have pending_four:
    "enc_pending spec_st = [?b0, ?b0, ?b0, ?b3]"
    using pending_eq bytes_four by simp
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RAdd (heap_bytes_word s pending 0 (4 :: 32 word))) spec_st)"
    using flush_pending_spec_four_add_break3[OF pending_four pending_break3]
          bytes_four
    by simp_all
  show ?thesis
    unfolding flush_pending'_def
    apply runs_to_vcg
    apply (rule runs_to_whileLoop_exn'[
      where R = "measure
        (\<lambda>((add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C), _).
          if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0)"
        and I = "\<lambda>r t.
          (r = Result (0, 0, sec) \<or>
           r = Result (0, 1, sec) \<or>
           r = Result (0, 2, sec) \<or>
           r = Result (0, 3, sec) \<or>
           r = Result (0, 4, sec)) \<and> t = s"])
       apply (clarsimp split: prod.splits)
     apply runs_to_vcg
     using pending_valid apply (simp add: word_less_nat_alt)
     apply (subst whileLoop_unroll)
     apply runs_to_vcg
     apply (auto simp: word_less_nat_alt word_le_nat_alt
                       pending_eq01 pending_eq02 pending_break3)
     subgoal
       apply runs_to_vcg
          using v0 apply simp
         using v1 apply simp
        using p1 apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using v2 p2 apply (auto simp: word_less_nat_alt word_le_nat_alt)
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using v3 p3_ne apply (auto simp: word_less_nat_alt word_le_nat_alt)
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       using p3_ne apply simp
       using p1 apply simp
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=1 in allE)
          apply simp
         apply (erule_tac x=2 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (erule_tac x=3 in allE)
         apply simp
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         apply (auto simp: word_less_nat_alt word_le_nat_alt)
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
          apply (erule_tac x=2 in allE)
          apply simp
         apply (erule_tac x=3 in allE)
         apply simp
       apply (subst whileLoop_unroll)
       apply runs_to_vcg
       apply (auto simp: word_less_nat_alt word_le_nat_alt)
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       subgoal
         apply (subst whileLoop_unroll)
         apply runs_to_vcg
         done
       done
     subgoal
       apply runs_to_vcg
       apply (erule_tac x=3 in allE)
       apply simp
       done
    apply (rule runs_to_liftE_bind_throw_result)
    apply (rule runs_to_weaken)
     apply (rule emit_add'_small_success_enc_sections_state_rel[
        where src_len = src_len])
                       apply (rule rel)
                      apply simp
                     apply simp
                    apply (rule sec_ok)
                   apply (rule inst_byte_fits)
                  apply (rule inst_byte_ptr)
                 apply (rule inst_byte_dist)
                apply (rule inst_byte_data_disj)
               apply (rule inst_byte_addr_disj)
              using inst_byte_pending_disj apply simp
             apply (rule data_fits)
            using data_valid apply simp
           using pending_valid apply simp
          using data_pending_disj apply simp
         using data_inj apply simp
        using data_prefix_disj apply simp
       apply (rule data_no_overflow)
      using data_inst_disj apply simp
     using data_addr_disj apply simp
    using pure_sections by (auto simp: enc_sections_state_rel_def)
qed

lemma flush_pending'_len_four_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 (4 :: 32 word)"
      and pending_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' (4 :: 32 word) s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat (4 :: 32 word).
           pending +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < (4 :: 32 word)"
      and data_valid: "\<forall>j < unat (4 :: 32 word).
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and data_pending_disj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
      and data_inj: "\<forall>i < unat (4 :: 32 word).
        \<forall>j < unat (4 :: 32 word).
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat (4 :: 32 word) < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < (4 :: 32 word) \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "flush_pending' sec data data_cap inst inst_cap pending (4 :: 32 word) \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?b0 = "heap_w8 s pending"
  let ?b1 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 1))"
  let ?b2 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 2))"
  let ?b3 = "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat 3))"
  have unat4[simp]: "unat (4 :: 32 word) = 4"
    by simp
  consider
    (run) "?b1 = ?b0" "?b2 = ?b0" "?b3 = ?b0"
  | (break1) "?b1 \<noteq> ?b0"
  | (break2) "?b1 = ?b0" "?b2 \<noteq> ?b0"
  | (break3) "?b1 = ?b0" "?b2 = ?b0" "?b3 \<noteq> ?b0"
    by blast
  then show ?thesis
  proof cases
    case run
    have pending_all_eq: "\<forall>j < unat (4 :: 32 word).
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
    proof (intro allI impI)
      fix j
      assume "j < unat (4 :: 32 word)"
      then have "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3"
        by auto
      then show "heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
          heap_w8 s pending"
        using run by auto
    qed
    show ?thesis
      by (rule flush_pending'_len_four_run_enc_sections_state_rel[
          OF rel pending_eq pending_all_eq pending_valid size sec_ok
             inst_byte_fits inst_byte_ptr inst_byte_dist
             inst_byte_data_disj inst_byte_addr_disj
             inst_varint_fits inst_varint_valid inst_varint_inj
             inst_varint_prefix_disj inst_varint_no_overflow
             inst_varint_data_disj inst_varint_addr_disj
             data_byte_fits data_byte_ptr data_byte_dist
             data_byte_inst_disj data_byte_addr_disj])
  next
    case break1
    show ?thesis
      by (rule flush_pending'_len_four_add_break1_enc_sections_state_rel[
          OF rel pending_eq break1 sec_ok
             inst_byte_fits inst_byte_ptr inst_byte_dist
             inst_byte_data_disj inst_byte_addr_disj inst_byte_pending_disj
             data_fits data_valid pending_valid data_pending_disj
             data_inj data_prefix_disj data_no_overflow
             data_inst_disj data_addr_disj])
  next
    case break2
    show ?thesis
      by (rule flush_pending'_len_four_add_break2_enc_sections_state_rel[
          OF rel pending_eq break2(1) break2(2) sec_ok
             inst_byte_fits inst_byte_ptr inst_byte_dist
             inst_byte_data_disj inst_byte_addr_disj inst_byte_pending_disj
             data_fits data_valid pending_valid data_pending_disj
             data_inj data_prefix_disj data_no_overflow
             data_inst_disj data_addr_disj])
  next
    case break3
    show ?thesis
      by (rule flush_pending'_len_four_add_break3_enc_sections_state_rel[
          OF rel pending_eq break3(1) break3(2) break3(3) sec_ok
             inst_byte_fits inst_byte_ptr inst_byte_dist
             inst_byte_data_disj inst_byte_addr_disj inst_byte_pending_disj
             data_fits data_valid pending_valid data_pending_disj
             data_inj data_prefix_disj data_no_overflow
             data_inst_disj data_addr_disj])
  qed
qed

lemma flush_pending'_replicate_run_inner_loop_from:
  fixes len :: "32 word"
  assumes start_lt: "start < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                  heap_w8 s pending);
              return (j + 1, if ret then 1 else 0)
           }) (start, 1) :: (32 word \<times> 32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure
      (\<lambda>((j :: 32 word, ret :: 32 word), _). unat len - unat j)"
      and I = "\<lambda>(j, ret) t.
        unat j \<le> unat len \<and>
        (ret \<noteq> 0 \<longleftrightarrow> j < len) \<and>
        t = s"])
     subgoal
       using start_lt by (simp add: word_less_nat_alt)
    subgoal
      using start_lt by unat_arith
   subgoal premises prems for r t
   proof -
     obtain j ret where r_def: "r = (j, ret)"
       by (cases r)
     have j_le: "unat j \<le> unat len"
       using prems r_def by auto
     have not_lt: "\<not> j < len"
       using prems r_def by auto
     have "unat len \<le> unat j"
       using not_lt by (simp add: word_less_nat_alt)
     then have j_eq: "j = len"
       using j_le by (metis antisym_conv word_unat.Rep_inject)
     have ret_eq: "ret = 0"
       using prems r_def by auto
     show ?thesis
       using prems r_def j_eq ret_eq by simp
   qed
  subgoal for r t
    apply (cases r)
    apply clarsimp
    subgoal for j ret
      apply runs_to_vcg
      subgoal
        using pending_valid[rule_format, of "unat (j + 1)"]
        by (simp add: word_less_nat_alt word_unat.Rep_inverse)
      subgoal
        by (rule unat_suc_le_of_word_less)
      subgoal
        using pending_all_eq[rule_format, of "unat (j + 1)"]
        by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
      subgoal
        by (simp add: unat_measure_decrease_of_word_less)
      done
    done
  done

lemma flush_pending'_replicate_run_inner_loop_from_Res:
  fixes len start :: "32 word"
  assumes start_lt: "start < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                  heap_w8 s pending);
              return (j + 1, if ret then 1 else 0)
           }) (start, 1) :: (32 word \<times> 32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t. r = (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_weaken[
    where Q = "\<lambda>r t. r = Result (len, 0) \<and> t = s"])
  apply (rule flush_pending'_replicate_run_inner_loop_from[
      OF start_lt pending_all_eq pending_valid])
  by auto

lemma flush_pending'_replicate_run_inner_loop_from_int:
  fixes len :: "32 word"
  assumes start_lt: "start < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                  heap_w8 s pending);
              return (j + 1, if ret then 1 else 0)
           }) (start, 1) :: (32 word \<times> int, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure
      (\<lambda>((j :: 32 word, ret :: int), _). unat len - unat j)"
      and I = "\<lambda>(j, ret) t.
        unat j \<le> unat len \<and>
        (ret \<noteq> 0 \<longleftrightarrow> j < len) \<and>
        t = s"])
     subgoal
       using start_lt by (simp add: word_less_nat_alt)
    subgoal
      using start_lt by unat_arith
   subgoal premises prems for r t
   proof -
     obtain j ret where r_def: "r = (j, ret)"
       by (cases r)
     have j_le: "unat j \<le> unat len"
       using prems r_def by auto
     have not_lt: "\<not> j < len"
       using prems r_def by auto
     have "unat len \<le> unat j"
       using not_lt by (simp add: word_less_nat_alt)
     then have j_eq: "j = len"
       using j_le by (metis antisym_conv word_unat.Rep_inject)
     have ret_eq: "ret = 0"
       using prems r_def by auto
     show ?thesis
       using prems r_def j_eq ret_eq by simp
   qed
  subgoal for r t
    apply (cases r)
    apply clarsimp
    subgoal for j ret
      apply runs_to_vcg
      subgoal
        using pending_valid[rule_format, of "unat (j + 1)"]
        by (simp add: word_less_nat_alt word_unat.Rep_inverse)
      subgoal
        by (rule unat_suc_le_of_word_less)
      subgoal
        using pending_all_eq[rule_format, of "unat (j + 1)"]
        by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
      subgoal
        by (simp add: unat_measure_decrease_of_word_less)
      done
    done
  done

lemma flush_pending'_replicate_run_inner_loop_from_Res_int:
  fixes len start :: "32 word"
  assumes start_lt: "start < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                  heap_w8 s pending);
              return (j + 1, if ret then 1 else 0)
           }) (start, 1) :: (32 word \<times> int, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t. r = (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_weaken[
    where Q = "\<lambda>r t. r = Result (len, 0) \<and> t = s"])
  apply (rule flush_pending'_replicate_run_inner_loop_from_int[
      OF start_lt pending_all_eq pending_valid])
  by auto

lemma flush_pending'_scan_inner_loop_bounds_from_Res_int:
  fixes len start :: "32 word"
  assumes start_lt: "start < len"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
              return (j + 1, if ret then 1 else 0)
           }) (start, 1) :: (32 word \<times> int, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t.
              \<exists>j. r = (j, 0) \<and> t = s \<and>
                unat start \<le> unat j \<and> unat j \<le> unat len \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure
      (\<lambda>((j :: 32 word, ret :: int), _). unat len - unat j)"
      and I = "\<lambda>(j, ret) t.
        unat start \<le> unat j \<and>
        unat j \<le> unat len \<and>
        (ret \<noteq> 0 \<longrightarrow> j < len) \<and>
        t = s"])
     subgoal
       using start_lt by (simp add: word_less_nat_alt)
    subgoal
      using start_lt by unat_arith
   subgoal premises prems for r t
   proof -
     obtain j ret where r_def: "r = (j, ret)"
       by (cases r)
     have ret_zero: "ret = 0"
       using prems r_def by auto
     show ?thesis
       using prems ret_zero r_def by auto
   qed
  subgoal for r t
    apply (cases r)
    apply clarsimp
    subgoal for j ret
      apply runs_to_vcg
      subgoal
        using pending_valid[rule_format, of "unat (j + 1)"]
        by (simp add: word_less_nat_alt word_unat.Rep_inverse)
      subgoal
        apply (subst unat_word_suc_of_less)
         apply assumption
        apply simp
        done
      subgoal
        by (simp add: unat_suc_le_of_word_less)
      subgoal
        by (simp add: unat_measure_decrease_of_word_less)
      done
    done
  done

lemma flush_pending'_replicate_run_inner_loop_from_Res_unat:
  fixes len start :: "32 word"
  assumes start_lt: "unat start < unat len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. unat (j + 1) < unat len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. unat (j + 1) < unat len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                  heap_w8 s pending);
              return (j + 1, if ret then 1 else 0)
           }) (start, 1) :: (32 word \<times> 32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t. r = (len, 0) \<and> t = s \<rbrace>"
proof -
  have start_word: "start < len"
    using start_lt by (simp add: word_less_nat_alt)
  show ?thesis
    using flush_pending'_replicate_run_inner_loop_from_Res
      [OF start_word pending_all_eq pending_valid]
    by (simp add: word_less_nat_alt)
qed

lemma flush_pending'_replicate_run_inner_loop_from_liftE:
  fixes len start :: "32 word"
  assumes start_lt: "start < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(liftE
           ((whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
             (\<lambda>(j, ret). do {
                x \<leftarrow> guard
                  (\<lambda>st. j + 1 < len \<longrightarrow>
                    IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
                ret \<leftarrow> gets
                  (\<lambda>st. j + 1 < len \<and>
                    heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                    heap_w8 s pending);
                return (j + 1, if ret then 1 else 0)
             }) (start, 1)) ::
              (32 word \<times> 32 word, lifted_globals) res_monad)
          :: ('e, 32 word \<times> 32 word, lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_liftE)
  apply (rule runs_to_weaken[
    OF flush_pending'_replicate_run_inner_loop_from_Res])
     apply (rule start_lt)
    apply (rule pending_all_eq)
    apply (rule pending_valid)
  by auto

lemma unat_suc_le_of_unat_less32:
  fixes i len :: "32 word"
  assumes "unat i < unat len"
  shows "unat (i + 1) \<le> unat len"
  using assms unat_suc_le_of_word_less[of i len]
  by (simp add: word_less_nat_alt)

lemma unat_measure_decrease_of_unat_less32:
  fixes i len :: "32 word"
  assumes "unat i < unat len"
  shows "unat len - unat (i + 1) < unat len - unat i"
  using assms unat_measure_decrease_of_word_less[of i len]
  by (simp add: word_less_nat_alt)

lemma word_suc_eq_of_unat_lt_not_unat_suc_lt32:
  fixes i len :: "32 word"
  assumes i_lt: "unat i < unat len"
      and suc_not_lt: "\<not> unat (i + 1) < unat len"
  shows "i + 1 = len"
proof -
  have suc_le: "unat (i + 1) \<le> unat len"
    by (rule unat_suc_le_of_unat_less32[OF i_lt])
  have len_le: "unat len \<le> unat (i + 1)"
    using suc_not_lt by simp
  then have "unat (i + 1) = unat len"
    using suc_le by simp
  then show ?thesis
    by (metis word_unat.Rep_inject)
qed

lemma all_prev_extend_word_suc:
  fixes j len :: "32 word"
  assumes j_lt: "j < len"
      and all_prev: "\<And>k. \<lbrakk> start \<le> k; k < unat j \<rbrakk> \<Longrightarrow> P k"
      and cur: "P (unat j)"
      and k_ge: "start \<le> k"
      and k_lt: "k < unat (j + 1)"
  shows "P k"
proof (cases "k < unat j")
  case True
  then show ?thesis
    using all_prev k_ge by blast
next
  case False
  have suc_unat: "unat (j + 1) = Suc (unat j)"
    using unat_word_suc_of_less[OF j_lt] .
  then have "k = unat j"
    using False k_lt by simp
  then show ?thesis
    using cur by simp
qed

lemma pending_all_eq_extend_word_suc:
  fixes j len :: "32 word"
  assumes j_lt: "j < len"
      and all_prev: "\<forall>k. start \<le> k \<and> k < unat j \<longrightarrow>
        heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      and cur: "heap_w8 s (pending +\<^sub>p uint j) = b"
      and k_ge: "start \<le> k"
      and k_lt: "k < unat (j + 1)"
  shows "heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
proof -
  have cur_at_unat:
    "heap_w8 s
      (pending +\<^sub>p uint ((0 :: 32 word) + of_nat (unat j))) = b"
    using cur by simp
  show ?thesis
    apply (rule all_prev_extend_word_suc[
      where P = "\<lambda>k. heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
        and j = j and len = len and start = start,
      OF j_lt _ cur_at_unat k_ge k_lt])
    using all_prev by blast
qed

lemma flush_pending_scan_inner_step_maximal:
  fixes j len :: "32 word"
    and ret :: int
    and start :: nat
    and pending :: "8 word ptr"
    and b :: byte
    and s :: lifted_globals
  defines "j' \<equiv> j + 1"
      and "ret' \<equiv>
        (if j + 1 < len \<and>
            heap_w8 s (pending +\<^sub>p uint (j + 1)) = b
         then (1 :: int) else 0)"
  assumes start_le: "start \<le> unat j"
      and j_le: "unat j \<le> unat len"
      and ret_run: "ret \<noteq> (0 :: int)"
      and ret_imp:
        "ret \<noteq> (0 :: int) \<longrightarrow>
          j < len \<and> heap_w8 s (pending +\<^sub>p uint j) = b"
      and all_prev:
        "\<forall>k. start \<le> k \<and> k < unat j \<longrightarrow>
          heap_w8 s
            (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
  shows "start \<le> unat j' \<and>
         unat j' \<le> unat len \<and>
         (ret' \<noteq> 0 \<longrightarrow>
          j' < len \<and> heap_w8 s (pending +\<^sub>p uint j') = b) \<and>
         (ret' = 0 \<longrightarrow>
          (j' < len \<longrightarrow>
            heap_w8 s (pending +\<^sub>p uint j') \<noteq> b)) \<and>
         (\<forall>k. start \<le> k \<and> k < unat j' \<longrightarrow>
          heap_w8 s
            (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b)"
proof -
  have j_lt: "j < len"
    using ret_run ret_imp by simp
  have cur: "heap_w8 s (pending +\<^sub>p uint j) = b"
    using ret_run ret_imp by simp
  have start_le_suc: "start \<le> unat j'"
    unfolding j'_def
    apply (subst unat_word_suc_of_less)
     apply (rule j_lt)
    using start_le by simp
  have suc_le_len: "unat j' \<le> unat len"
    unfolding j'_def
    by (rule unat_suc_le_of_word_less[OF j_lt])
  have ret_nonzero:
    "ret' \<noteq> 0 \<longrightarrow>
      j' < len \<and> heap_w8 s (pending +\<^sub>p uint j') = b"
    unfolding ret'_def j'_def by auto
  have ret_zero:
    "ret' = 0 \<longrightarrow>
      (j' < len \<longrightarrow> heap_w8 s (pending +\<^sub>p uint j') \<noteq> b)"
    unfolding ret'_def j'_def by auto
  have all_suc:
    "\<forall>k. start \<le> k \<and> k < unat j' \<longrightarrow>
      heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
  proof safe
    fix k
    assume k_ge: "start \<le> k"
       and k_lt: "k < unat j'"
    show "heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      unfolding j'_def
      apply (rule pending_all_eq_extend_word_suc[
        OF j_lt all_prev cur k_ge])
      using k_lt unfolding j'_def .
  qed
  show ?thesis
    using start_le_suc suc_le_len ret_nonzero ret_zero all_suc by blast
qed

definition flush_pending_scan_inner_inv ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> byte \<Rightarrow> nat \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> int \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "flush_pending_scan_inner_inv s pending b start len j ret t \<longleftrightarrow>
     start \<le> unat j \<and>
     unat j \<le> unat len \<and>
     (ret \<noteq> 0 \<longrightarrow>
       j < len \<and> heap_w8 s (pending +\<^sub>p uint j) = b) \<and>
     (ret = 0 \<longrightarrow>
       (j < len \<longrightarrow> heap_w8 s (pending +\<^sub>p uint j) \<noteq> b)) \<and>
     (\<forall>k. start \<le> k \<and> k < unat j \<longrightarrow>
       heap_w8 s
         (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b) \<and>
     t = s"

lemma flush_pending_scan_inner_inv_init:
  assumes start_lt: "start < len"
      and start_eq: "heap_w8 s (pending +\<^sub>p uint start) = b"
  shows "flush_pending_scan_inner_inv s pending b (unat start) len
           start (1 :: int) s"
  using start_lt start_eq
  by (auto simp: flush_pending_scan_inner_inv_def word_less_nat_alt)

lemma flush_pending_scan_inner_inv_init_suc:
  fixes i len :: "32 word"
  assumes i_lt_len: "i < len"
      and cur_eq: "heap_w8 s (pending +\<^sub>p uint i) = b"
  shows "flush_pending_scan_inner_inv s pending b (unat i) len
          (i + 1)
          (if i + 1 < len \<and>
              heap_w8 s (pending +\<^sub>p uint (i + 1)) = b
           then (1 :: int) else 0)
          s"
proof -
  have suc_unat: "unat (i + 1) = Suc (unat i)"
    using unat_word_suc_of_less[OF i_lt_len] .
  have suc_le_len: "unat (i + 1) \<le> unat len"
    by (rule unat_suc_le_of_word_less[OF i_lt_len])
  have all_prev:
    "\<forall>k. unat i \<le> k \<and> k < unat (i + 1) \<longrightarrow>
      heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
  proof safe
    fix k
    assume "unat i \<le> k" and "k < unat (i + 1)"
    then have k_eq: "k = unat i"
      using suc_unat by simp
    show "heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      using cur_eq k_eq by (simp add: word_unat.Rep_inverse)
  qed
  show ?thesis
    using suc_unat suc_le_len all_prev
    by (auto simp: flush_pending_scan_inner_inv_def)
qed

lemma flush_pending_scan_inner_inv_exit:
  assumes inv:
        "flush_pending_scan_inner_inv s pending b start len j ret t"
      and ret_zero: "ret = (0 :: int)"
  shows "\<exists>j'. (j, ret) = (j', 0) \<and> t = s \<and>
          start \<le> unat j' \<and> unat j' \<le> unat len \<and>
          (\<forall>k. start \<le> k \<and> k < unat j' \<longrightarrow>
            heap_w8 s
              (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b) \<and>
          (j' < len \<longrightarrow> heap_w8 s (pending +\<^sub>p uint j') \<noteq> b)"
  using inv ret_zero
  by (auto simp: flush_pending_scan_inner_inv_def)

lemma flush_pending_scan_inner_inv_step:
  assumes inv:
        "flush_pending_scan_inner_inv s pending b start len j ret t"
      and ret_run: "ret \<noteq> (0 :: int)"
  shows "flush_pending_scan_inner_inv s pending b start len
          (j + 1)
          (if j + 1 < len \<and>
              heap_w8 s (pending +\<^sub>p uint (j + 1)) = b
           then (1 :: int) else 0)
          t"
proof -
  have start_le: "start \<le> unat j"
      and j_le: "unat j \<le> unat len"
      and ret_imp:
        "ret \<noteq> 0 \<longrightarrow>
          j < len \<and> heap_w8 s (pending +\<^sub>p uint j) = b"
      and all_prev:
        "\<forall>k. start \<le> k \<and> k < unat j \<longrightarrow>
          heap_w8 s
            (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      and t_eq: "t = s"
    using inv by (auto simp: flush_pending_scan_inner_inv_def)
  have j_lt: "j < len"
    using ret_run ret_imp by simp
  have cur: "heap_w8 s (pending +\<^sub>p uint j) = b"
    using ret_run ret_imp by simp
  have start_le_suc: "start \<le> unat (j + 1)"
    apply (subst unat_word_suc_of_less)
     apply (rule j_lt)
    using start_le by simp
  have suc_le_len: "unat (j + 1) \<le> unat len"
    by (rule unat_suc_le_of_word_less[OF j_lt])
  have all_suc:
    "\<forall>k. start \<le> k \<and> k < unat (j + 1) \<longrightarrow>
      heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
  proof safe
    fix k
    assume k_ge: "start \<le> k"
       and k_lt: "k < unat (j + 1)"
    show "heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      by (rule pending_all_eq_extend_word_suc[
          OF j_lt all_prev cur k_ge k_lt])
  qed
  show ?thesis
    using start_le_suc suc_le_len all_suc t_eq
    by (auto simp: flush_pending_scan_inner_inv_def)
qed

lemma flush_pending_scan_inner_inv_step_true:
  assumes inv:
        "flush_pending_scan_inner_inv s pending b start len j ret t"
      and ret_run: "ret \<noteq> (0 :: int)"
      and next_lt: "j + 1 < len"
      and next_eq: "heap_w8 t (pending +\<^sub>p uint (j + 1)) = b"
  shows "flush_pending_scan_inner_inv s pending b start len
          (j + 1) (1 :: int) t"
proof -
  have t_eq: "t = s"
    using inv by (simp add: flush_pending_scan_inner_inv_def)
  show ?thesis
    using flush_pending_scan_inner_inv_step[OF inv ret_run]
          next_lt next_eq t_eq
    by simp
qed

lemma flush_pending_scan_inner_inv_step_false:
  assumes inv:
        "flush_pending_scan_inner_inv s pending b start len j ret t"
      and ret_run: "ret \<noteq> (0 :: int)"
      and next_ne:
        "j + 1 < len \<longrightarrow>
          heap_w8 t (pending +\<^sub>p uint (j + 1)) \<noteq> b"
  shows "flush_pending_scan_inner_inv s pending b start len
          (j + 1) (0 :: int) t"
proof -
  have t_eq: "t = s"
    using inv by (simp add: flush_pending_scan_inner_inv_def)
  show ?thesis
    using flush_pending_scan_inner_inv_step[OF inv ret_run]
          next_ne t_eq
    by auto
qed

lemma flush_pending'_scan_inner_loop_maximal_from_Res_int:
  fixes len start :: "32 word"
  assumes start_lt: "start < len"
      and start_eq:
        "heap_w8 s (pending +\<^sub>p uint start) = b"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
              return (j + 1, if ret then 1 else 0)
           }) (start, 1) :: (32 word \<times> int, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t.
              \<exists>j. r = (j, 0) \<and> t = s \<and>
                unat start \<le> unat j \<and> unat j \<le> unat len \<and>
                (\<forall>k. unat start \<le> k \<and> k < unat j \<longrightarrow>
                  heap_w8 s
                    (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b) \<and>
                (j < len \<longrightarrow>
                  heap_w8 s (pending +\<^sub>p uint j) \<noteq> b) \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure
      (\<lambda>((j :: 32 word, ret :: int), _). unat len - unat j)"
      and I = "\<lambda>(j, ret) t.
        flush_pending_scan_inner_inv s pending b (unat start) len j ret t"])
    subgoal
       by simp
    subgoal
       using flush_pending_scan_inner_inv_init[OF start_lt start_eq]
       by simp
   subgoal premises prems for r t
   proof -
     obtain j ret where r_def: "r = (j, ret)"
       by (cases r)
     have inv:
       "flush_pending_scan_inner_inv s pending b (unat start) len j ret t"
       using prems r_def by auto
     have ret_zero: "ret = (0 :: int)"
       using prems r_def by auto
     show ?thesis
       using flush_pending_scan_inner_inv_exit[OF inv ret_zero] r_def
       by auto
   qed
  subgoal for r t
    apply (cases r)
    apply clarsimp
    subgoal for j ret
      apply runs_to_vcg
      subgoal
        using pending_valid[rule_format, of "unat (j + 1)"]
        by (auto simp: word_less_nat_alt word_unat.Rep_inverse
                       flush_pending_scan_inner_inv_def)
      subgoal
        by (rule flush_pending_scan_inner_inv_step_true)
           auto
      subgoal
        using unat_measure_decrease_of_word_less[of j len]
        by (auto simp: flush_pending_scan_inner_inv_def)
      subgoal
        by (rule flush_pending_scan_inner_inv_step_false)
           auto
      subgoal
        using unat_measure_decrease_of_word_less[of j len]
        by (auto simp: flush_pending_scan_inner_inv_def)
      done
    done
  done

lemma flush_pending'_scan_from_Res_int:
  fixes len i :: "32 word"
  assumes i_lt_len: "i < len"
      and cur_eq: "heap_w8 s (pending +\<^sub>p uint i) = b"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "((do {
            j \<leftarrow> return (i + 1);
            ret \<leftarrow> do {
              x \<leftarrow> guard
                (\<lambda>st. j < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint j));
              gets
                (\<lambda>st. if j < len \<and>
                  heap_w8 st (pending +\<^sub>p uint j) = b
                 then (1 :: int) else 0)
            };
            whileLoop (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
              (\<lambda>(j, ret). do {
                 x \<leftarrow> guard
                   (\<lambda>st. j + 1 < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
                 ret \<leftarrow> gets
                   (\<lambda>st. j + 1 < len \<and>
                     heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                 return (j + 1, if ret then 1 else 0)
              }) (j, ret)
          }) :: (32 word \<times> int, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t.
              \<exists>j. r = (j, 0) \<and> t = s \<and>
                i < j \<and> j \<le> len \<and>
                (\<forall>k. unat i \<le> k \<and> k < unat j \<longrightarrow>
                  heap_w8 s
                    (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b) \<and>
                (j < len \<longrightarrow>
                  heap_w8 s (pending +\<^sub>p uint j) \<noteq> b) \<rbrace>"
  apply runs_to_vcg
  subgoal
    using pending_valid[rule_format, of "unat (i + 1)"]
    by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
  apply (rule runs_to_whileLoop_res'[
    where R = "measure
      (\<lambda>((j :: 32 word, ret :: int), _). unat len - unat j)"
      and I = "\<lambda>(j, ret) t.
        flush_pending_scan_inner_inv s pending b (unat i) len j ret t \<and>
        unat (i + 1) \<le> unat j"])
    subgoal
      by simp
    subgoal
      using flush_pending_scan_inner_inv_init_suc[OF i_lt_len cur_eq]
      by simp
   subgoal premises prems for r t
   proof -
     obtain j ret where r_def: "r = (j, ret)"
       by (cases r)
     have inv:
       "flush_pending_scan_inner_inv s pending b (unat i) len j ret t"
       using prems r_def by auto
     have lower: "unat (i + 1) \<le> unat j"
       using prems r_def by auto
     have ret_zero: "ret = (0 :: int)"
       using prems r_def by auto
     obtain j' where pair: "(j, ret) = (j', 0)"
        and t_eq: "t = s"
        and i_le_j: "unat i \<le> unat j'"
        and j_le_len_nat: "unat j' \<le> unat len"
        and all_eq:
          "\<forall>k. unat i \<le> k \<and> k < unat j' \<longrightarrow>
            heap_w8 s
              (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
        and stop:
          "j' < len \<longrightarrow> heap_w8 s (pending +\<^sub>p uint j') \<noteq> b"
       using flush_pending_scan_inner_inv_exit[OF inv ret_zero] by blast
     have j_eq: "j = j'"
       using pair by simp
     have i_lt_j: "i < j'"
     proof -
       have "unat i < unat (i + 1)"
         using i_lt_len unat_word_suc_of_less[OF i_lt_len] by simp
       also have "... \<le> unat j'"
         using lower j_eq by simp
       finally show ?thesis
         by (simp add: word_less_nat_alt)
     qed
     have j_le_len: "j' \<le> len"
       using j_le_len_nat by (simp add: word_le_nat_alt)
     show ?thesis
       using r_def pair t_eq i_lt_j j_le_len all_eq stop
       by auto
   qed
  subgoal for r t
    apply (cases r)
    apply clarsimp
    subgoal for j ret
      apply runs_to_vcg
      subgoal
        using pending_valid[rule_format, of "unat (j + 1)"]
        by (auto simp: word_less_nat_alt word_unat.Rep_inverse
                       flush_pending_scan_inner_inv_def)
      subgoal
        by (rule flush_pending_scan_inner_inv_step_true)
           auto
      subgoal
        using unat_word_suc_of_less[of j len]
        by (auto simp: flush_pending_scan_inner_inv_def)
      subgoal
        using unat_measure_decrease_of_word_less[of j len]
        by (auto simp: flush_pending_scan_inner_inv_def)
      subgoal
        by (rule flush_pending_scan_inner_inv_step_false)
           auto
      subgoal
        using unat_word_suc_of_less[of j len]
        by (auto simp: flush_pending_scan_inner_inv_def)
      subgoal
        using unat_measure_decrease_of_word_less[of j len]
        by (auto simp: flush_pending_scan_inner_inv_def)
      done
    done
  subgoal premises prems
  proof -
    have i_lt_suc: "i < i + 1"
      using i_lt_len unat_word_suc_of_less[OF i_lt_len]
      by (simp add: word_less_nat_alt)
    have suc_le_len: "i + 1 \<le> len"
      using unat_suc_le_of_word_less[OF i_lt_len]
      by (simp add: word_le_nat_alt)
    have suc_unat: "unat (i + 1) = Suc (unat i)"
      using unat_word_suc_of_less[OF i_lt_len] .
    have all_eq:
      "\<forall>k. unat i \<le> k \<and> k < unat (i + 1) \<longrightarrow>
        heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
    proof safe
      fix k
      assume "unat i \<le> k" and "k < unat (i + 1)"
      then have k_eq: "k = unat i"
        using suc_unat by simp
      show "heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
        using cur_eq k_eq by (simp add: word_unat.Rep_inverse)
    qed
    show ?thesis
      apply (subst whileLoop_unroll)
      using prems i_lt_suc suc_le_len all_eq
      by (auto simp: word_unat.Rep_inverse)
  qed
  done

lemma flush_pending'_scan_from_Res_int_pending_run_end:
  fixes len i :: "32 word"
  assumes i_lt_len: "i < len"
      and cur_eq: "heap_w8 s (pending +\<^sub>p uint i) = b"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "((do {
            j \<leftarrow> return (i + 1);
            ret \<leftarrow> do {
              x \<leftarrow> guard
                (\<lambda>st. j < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint j));
              gets
                (\<lambda>st. if j < len \<and>
                  heap_w8 st (pending +\<^sub>p uint j) = b
                 then (1 :: int) else 0)
            };
            whileLoop (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
              (\<lambda>(j, ret). do {
                 x \<leftarrow> guard
                   (\<lambda>st. j + 1 < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
                 ret \<leftarrow> gets
                   (\<lambda>st. j + 1 < len \<and>
                     heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                 return (j + 1, if ret then 1 else 0)
              }) (j, ret)
          }) :: (32 word \<times> int, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t.
              \<exists>j. r = (j, 0) \<and> t = s \<and>
                i < j \<and> j \<le> len \<and>
                pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
                  unat j \<and>
                (\<forall>k. unat i \<le> k \<and> k < unat j \<longrightarrow>
                  heap_w8 s
                    (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b) \<and>
                (j < len \<longrightarrow>
                  heap_w8 s (pending +\<^sub>p uint j) \<noteq> b) \<rbrace>"
  apply (rule runs_to_weaken[
    OF flush_pending'_scan_from_Res_int[
      OF i_lt_len cur_eq pending_valid]])
  apply clarsimp
  subgoal premises prems for j
  proof -
    have i_lt_j: "i < j"
      using prems by simp
    have j_le_len: "j \<le> len"
      using prems by simp
    have all_eq:
      "\<forall>k. unat i \<le> k \<and> k < unat j \<longrightarrow>
        heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      using prems by simp
    have stop:
      "j < len \<longrightarrow> heap_w8 s (pending +\<^sub>p uint j) \<noteq> b"
      using prems by simp
    show ?thesis
    proof (rule pending_run_end_eq_heap_scan[OF i_lt_j j_le_len])
      fix k
      assume i_le_k: "unat i \<le> k" and k_lt_j: "k < unat j"
      show "heap_w8 s
              (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) =
            heap_w8 s (pending +\<^sub>p uint i)"
        using all_eq i_le_k k_lt_j cur_eq by auto
    next
      assume j_lt_len: "j < len"
      show "heap_w8 s (pending +\<^sub>p uint j) \<noteq>
            heap_w8 s (pending +\<^sub>p uint i)"
        using stop j_lt_len cur_eq by auto
    qed
  qed
  done

lemma pending_run_end_eq_heap_scan_from_suc:
  fixes i j len :: "32 word"
  assumes i_lt_len: "i < len"
      and start_le_j: "unat (i + 1) \<le> unat j"
      and j_le_len_nat: "unat j \<le> unat len"
      and cur_eq: "heap_w8 s (pending +\<^sub>p uint i) = b"
      and all_eq_tail:
        "\<forall>k. unat (i + 1) \<le> k \<and> k < unat j \<longrightarrow>
          heap_w8 s
            (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
      and stop:
        "j < len \<longrightarrow> heap_w8 s (pending +\<^sub>p uint j) \<noteq> b"
  shows "i < j \<and> j \<le> len \<and>
         pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
           unat j"
proof -
  have suc_unat: "unat (i + 1) = Suc (unat i)"
    using unat_word_suc_of_less[OF i_lt_len] .
  have i_lt_j: "i < j"
  proof -
    have "unat i < unat (i + 1)"
      using suc_unat by simp
    also have "... \<le> unat j"
      by (rule start_le_j)
    finally show ?thesis
      by (simp add: word_less_nat_alt)
  qed
  have j_le_len: "j \<le> len"
    using j_le_len_nat by (simp add: word_le_nat_alt)
  have all_eq:
    "\<And>k. \<lbrakk>unat i \<le> k; k < unat j\<rbrakk> \<Longrightarrow>
      heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) =
      heap_w8 s (pending +\<^sub>p uint i)"
  proof -
    fix k
    assume i_le_k: "unat i \<le> k" and k_lt_j: "k < unat j"
    show "heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) =
      heap_w8 s (pending +\<^sub>p uint i)"
    proof (cases "k = unat i")
      case True
      then show ?thesis
        by simp
    next
      case False
      then have "unat (i + 1) \<le> k"
        using i_le_k suc_unat by simp
      then have "heap_w8 s
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) = b"
        using all_eq_tail k_lt_j by auto
      then show ?thesis
        using cur_eq by simp
    qed
  qed
  have stop_i:
    "j < len \<Longrightarrow>
      heap_w8 s (pending +\<^sub>p uint j) \<noteq>
      heap_w8 s (pending +\<^sub>p uint i)"
    using stop cur_eq by auto
  have run_end:
    "pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
     unat j"
    by (rule pending_run_end_eq_heap_scan[
        OF i_lt_j j_le_len all_eq stop_i])
  show ?thesis
    using i_lt_j j_le_len run_end by simp
qed

lemma pending_run_end_eq_heap_scan_suc_stop:
  fixes i len :: "32 word"
  assumes i_lt_len: "i < len"
      and cur_eq: "heap_w8 s (pending +\<^sub>p uint i) = b"
      and stop:
        "i + 1 < len \<longrightarrow>
          heap_w8 s (pending +\<^sub>p uint (i + 1)) \<noteq> b"
  shows "i < i + 1 \<and> i + 1 \<le> len \<and>
         pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
           unat (i + 1)"
proof -
  have i_lt_suc: "i < i + 1"
    using i_lt_len unat_word_suc_of_less[OF i_lt_len]
    by (simp add: word_less_nat_alt)
  have suc_le_len: "i + 1 \<le> len"
    using unat_suc_le_of_word_less[OF i_lt_len]
    by (simp add: word_le_nat_alt)
  have suc_unat: "unat (i + 1) = Suc (unat i)"
    using unat_word_suc_of_less[OF i_lt_len] .
  have all_eq:
    "\<And>k. \<lbrakk>unat i \<le> k; k < unat (i + 1)\<rbrakk> \<Longrightarrow>
      heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) =
      heap_w8 s (pending +\<^sub>p uint i)"
  proof -
    fix k
    assume "unat i \<le> k" and "k < unat (i + 1)"
    then have "k = unat i"
      using suc_unat by simp
    then show "heap_w8 s
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat k)) =
      heap_w8 s (pending +\<^sub>p uint i)"
      by simp
  qed
  have stop_i:
    "i + 1 < len \<Longrightarrow>
      heap_w8 s (pending +\<^sub>p uint (i + 1)) \<noteq>
      heap_w8 s (pending +\<^sub>p uint i)"
    using stop cur_eq by auto
  have run_end:
    "pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
     unat (i + 1)"
    by (rule pending_run_end_eq_heap_scan[
        OF i_lt_suc suc_le_len all_eq stop_i])
  show ?thesis
    using i_lt_suc suc_le_len run_end by simp
qed

lemma flush_pending'_scan_from_liftE_split_pending_run_end:
  fixes len i :: "32 word"
  assumes i_lt_len: "i < len"
      and cur_eq: "heap_w8 s (pending +\<^sub>p uint i) = b"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "((do {
            j \<leftarrow> return (i + 1);
            ret \<leftarrow> liftE
              ((do {
                 x \<leftarrow> guard
                   (\<lambda>st. j < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint j));
                 gets
                   (\<lambda>st. if j < len \<and>
                     heap_w8 st (pending +\<^sub>p uint j) = b
                    then (1 :: int) else 0)
               }) :: (int, lifted_globals) res_monad);
            liftE
              ((whileLoop
                (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
                (\<lambda>(j, ret). do {
                   x \<leftarrow> guard
                     (\<lambda>st. j + 1 < len \<longrightarrow>
                       IS_VALID(8 word) st
                         (pending +\<^sub>p uint (j + 1)));
                   ret \<leftarrow> gets
                     (\<lambda>st. j + 1 < len \<and>
                       heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                   return (j + 1, if ret then 1 else 0)
                })
                (j, ret)) :: (32 word \<times> int, lifted_globals) res_monad)
          }) :: ('e, 32 word \<times> int, lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              \<exists>j. r = Result (j, 0) \<and> t = s \<and>
                i < j \<and> j \<le> len \<and>
                pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
                  unat j \<rbrace>"
  apply runs_to_vcg
  subgoal
    using pending_valid[rule_format, of "unat (i + 1)"]
    by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
  subgoal
    apply (rule runs_to_weaken[
      OF flush_pending'_scan_inner_loop_maximal_from_Res_int])
       apply assumption
      apply assumption
     apply (rule pending_valid)
    apply clarsimp
    apply (rule pending_run_end_eq_heap_scan_from_suc[
      OF i_lt_len])
        apply assumption
       apply assumption
      apply (rule cur_eq)
     apply simp
    apply simp
    done
  subgoal
    apply (subst whileLoop_unroll)
    using pending_run_end_eq_heap_scan_suc_stop[OF i_lt_len cur_eq]
    by auto
  done

lemma flush_pending'_scan_tail_from_liftE_split_pending_run_end:
  fixes len i :: "32 word"
  assumes i_lt_len: "i < len"
      and cur_eq: "heap_w8 s (pending +\<^sub>p uint i) = b"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "((do {
            ret \<leftarrow> liftE
              ((do {
                 x \<leftarrow> guard
                   (\<lambda>st. i + 1 < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint (i + 1)));
                 gets
                   (\<lambda>st. if i + 1 < len \<and>
                     heap_w8 st (pending +\<^sub>p uint (i + 1)) = b
                    then (1 :: int) else 0)
               }) :: (int, lifted_globals) res_monad);
            liftE
              ((whileLoop
                (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
                (\<lambda>(j, ret). do {
                   x \<leftarrow> guard
                     (\<lambda>st. j + 1 < len \<longrightarrow>
                       IS_VALID(8 word) st
                         (pending +\<^sub>p uint (j + 1)));
                   ret \<leftarrow> gets
                     (\<lambda>st. j + 1 < len \<and>
                       heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                   return (j + 1, if ret then 1 else 0)
                })
                (i + 1, ret)) :: (32 word \<times> int, lifted_globals) res_monad)
          }) :: ('e, 32 word \<times> int, lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              \<exists>j. r = Result (j, 0) \<and> t = s \<and>
                i < j \<and> j \<le> len \<and>
                pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
                  unat j \<rbrace>"
  using flush_pending'_scan_from_liftE_split_pending_run_end[
      OF i_lt_len cur_eq pending_valid, where ?'e = 'e]
  by simp

lemma heap_bytes_word_frame_heap_w8_zero:
  fixes i len :: "32 word"
  assumes bytes:
        "heap_bytes_word t pending 0 len =
         heap_bytes_word s pending 0 len"
      and i_lt_len: "i < len"
  shows "heap_w8 t (pending +\<^sub>p uint i) =
         heap_w8 s (pending +\<^sub>p uint i)"
proof -
  have idx_lt: "unat i < unat len"
    using i_lt_len by (simp add: word_less_nat_alt)
  have nth_eq:
    "heap_bytes_word t pending 0 len ! unat i =
     heap_bytes_word s pending 0 len ! unat i"
    using arg_cong[OF bytes, of "\<lambda>xs. xs ! unat i"] .
  show ?thesis
    using nth_eq idx_lt
    by (simp add: heap_bytes_word_nth word_unat.Rep_inverse)
qed

definition flush_pending_outer_run_state ::
  "nat \<Rightarrow> lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> 8 word \<Rightarrow> enc_full_state \<Rightarrow>
   enc_full_state" where
  "flush_pending_outer_run_state src_len s0 pending add_start i j b
      loop_st =
     emit_inst_spec src_len (RRun b (unat (j - i)))
      (if add_start < i
       then emit_inst_spec src_len
         (RAdd (heap_bytes_word s0 pending add_start (i - add_start)))
         loop_st
       else loop_st)"

definition flush_pending_outer_tail_state ::
  "nat \<Rightarrow> lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word \<Rightarrow> enc_full_state \<Rightarrow> enc_full_state" where
  "flush_pending_outer_tail_state src_len s0 pending len add_start
      loop_st =
     ((if add_start < len
       then emit_inst_spec src_len
         (RAdd (heap_bytes_word s0 pending add_start (len - add_start)))
         loop_st
       else loop_st)\<lparr>enc_pending := []\<rparr>)"

definition flush_pending_outer_run_branch ::
  "8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   8 word \<Rightarrow> sections_t_C \<Rightarrow>
   (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
     lifted_globals) exn_monad" where
  "flush_pending_outer_run_branch data data_cap inst inst_cap pending
      add_start i j b sec_cur = do {
     sec_cur \<leftarrow> condition (\<lambda>st. add_start < i)
       (do {
          sec_cur \<leftarrow> liftE
            (emit_add' sec_cur data data_cap inst inst_cap pending
              add_start (i - add_start));
          unless (sections_t_C.err_C sec_cur = ENC_OK)
            (throw sec_cur);
          return sec_cur
       })
       (return sec_cur);
     sec_cur \<leftarrow> liftE
       (emit_run' sec_cur data data_cap inst inst_cap b (j - i));
     unless (sections_t_C.err_C sec_cur = ENC_OK)
       (throw sec_cur);
     return (j, j, sec_cur)
   }"

definition flush_pending_outer_body ::
  "8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word \<times> 32 word \<times> sections_t_C \<Rightarrow>
   (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
     lifted_globals) exn_monad" where
  "flush_pending_outer_body data data_cap inst inst_cap pending len =
    (\<lambda>(add_start, i, sec_cur). do {
      guard (\<lambda>st. IS_VALID(8 word) st (pending +\<^sub>p uint i));
      b \<leftarrow> gets (\<lambda>st. heap_w8 st (pending +\<^sub>p uint i));
      j \<leftarrow> return (i + 1);
      ret \<leftarrow> liftE
        ((do {
           guard (\<lambda>st. j < len \<longrightarrow>
             IS_VALID(8 word) st (pending +\<^sub>p uint j));
           gets (\<lambda>st. if j < len \<and>
             heap_w8 st (pending +\<^sub>p uint j) = b
            then (1 :: int) else 0)
         }) :: (int, lifted_globals) res_monad);
      (j, ret) \<leftarrow> liftE
        ((whileLoop
          (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
          (\<lambda>(j, ret). do {
             j \<leftarrow> return (j + 1);
             x \<leftarrow> guard (\<lambda>st. j < len \<longrightarrow>
               IS_VALID(8 word) st
                 (pending +\<^sub>p uint j));
             ret \<leftarrow> gets (\<lambda>st. j < len \<and>
               heap_w8 st (pending +\<^sub>p uint j) = b);
             return (j, if ret then 1 else 0)
          })
          (j, ret)) :: (32 word \<times> int, lifted_globals) res_monad);
      condition (\<lambda>st. (4 :: 32 word) \<le> j - i)
        (flush_pending_outer_run_branch data data_cap inst inst_cap pending
          add_start i j b sec_cur)
        (return (add_start, j, sec_cur))
    })"

definition flush_pending_outer_tail ::
  "8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> sections_t_C \<Rightarrow>
   (sections_t_C, lifted_globals) res_monad" where
  "flush_pending_outer_tail data data_cap inst inst_cap pending len
      add_start sec_cur =
    condition (\<lambda>st. add_start < len)
      (emit_add' sec_cur data data_cap inst inst_cap pending
        add_start (len - add_start))
      (return sec_cur)"

definition flush_pending_outer_loop_inv ::
  "nat \<Rightarrow> lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow>
   8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   enc_full_state \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   sections_t_C \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
      spec_st add_start i sec_cur t \<longleftrightarrow>
     add_start \<le> i \<and>
     i \<le> len \<and>
     heap_typing t = heap_typing s0 \<and>
     heap_bytes_word t pending 0 len =
       heap_bytes_word s0 pending 0 len \<and>
     sections_t_C.err_C sec_cur = ENC_OK \<and>
     (\<exists>loop_st.
       enc_sections_state_rel t data inst addr sec_cur loop_st \<and>
       flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
         (unat add_start) (unat i) loop_st =
       flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
         0 0 spec_st)"

definition flush_pending_outer_emit_pre ::
  "nat \<Rightarrow> lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow>
   32 word \<Rightarrow> enc_full_state \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   sections_t_C \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "flush_pending_outer_emit_pre src_len s0 data data_cap inst inst_cap
      addr pending len spec_st add_start i sec_cur t \<longleftrightarrow>
     ((\<forall>j b loop_st.
        i < j \<longrightarrow>
        j \<le> len \<longrightarrow>
        pending_run_end (heap_bytes_word s0 pending 0 len) (unat i) =
          unat j \<longrightarrow>
        (4 :: 32 word) \<le> j - i \<longrightarrow>
        b = heap_w8 s0 (pending +\<^sub>p uint i) \<longrightarrow>
        enc_sections_state_rel t data inst addr sec_cur loop_st \<longrightarrow>
        flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
          (unat add_start) (unat i) loop_st =
        flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
          0 0 spec_st \<longrightarrow>
        flush_pending_outer_run_branch data data_cap inst inst_cap pending
          add_start i j b sec_cur \<bullet> t
        \<lbrace> \<lambda>r u.
             \<exists>sec'.
               r = Result (j, j, sec') \<and>
               sections_t_C.err_C sec' = ENC_OK \<and>
               heap_bytes_word u pending 0 len =
                 heap_bytes_word s0 pending 0 len \<and>
               heap_typing u = heap_typing s0 \<and>
               enc_sections_state_rel u data inst addr sec'
                 (flush_pending_outer_run_state src_len s0 pending
                   add_start i j b loop_st) \<rbrace>) \<and>
      (\<forall>loop_st.
        i = len \<longrightarrow>
        enc_sections_state_rel t data inst addr sec_cur loop_st \<longrightarrow>
        flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
          (unat add_start) (unat len) loop_st =
        flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
          0 0 spec_st \<longrightarrow>
        flush_pending_outer_tail data data_cap inst inst_cap pending len
          add_start sec_cur \<bullet> t
        \<lbrace> \<lambda>Res sec' u.
             enc_sections_state_rel u data inst addr sec'
               (flush_pending_outer_tail_state src_len s0 pending len
                 add_start loop_st) \<and>
             heap_typing u = heap_typing s0 \<rbrace>))"

lemma flush_pending_outer_emit_preI:
  assumes run:
        "\<And>j b loop_st. \<lbrakk>
          i < j;
          j \<le> len;
          pending_run_end (heap_bytes_word s0 pending 0 len) (unat i) =
            unat j;
          (4 :: 32 word) \<le> j - i;
          b = heap_w8 s0 (pending +\<^sub>p uint i);
          enc_sections_state_rel t data inst addr sec_cur loop_st;
          flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
            (unat add_start) (unat i) loop_st =
          flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
            0 0 spec_st
        \<rbrakk> \<Longrightarrow>
          flush_pending_outer_run_branch data data_cap inst inst_cap pending
            add_start i j b sec_cur \<bullet> t
          \<lbrace> \<lambda>r u.
               \<exists>sec'.
                 r = Result (j, j, sec') \<and>
                 sections_t_C.err_C sec' = ENC_OK \<and>
                 heap_bytes_word u pending 0 len =
                   heap_bytes_word s0 pending 0 len \<and>
                 heap_typing u = heap_typing s0 \<and>
                 enc_sections_state_rel u data inst addr sec'
                   (flush_pending_outer_run_state src_len s0 pending
                     add_start i j b loop_st) \<rbrace>"
      and tail:
        "\<And>loop_st. \<lbrakk>
          i = len;
          enc_sections_state_rel t data inst addr sec_cur loop_st;
          flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
            (unat add_start) (unat len) loop_st =
          flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
            0 0 spec_st
        \<rbrakk> \<Longrightarrow>
          flush_pending_outer_tail data data_cap inst inst_cap pending len
            add_start sec_cur \<bullet> t
          \<lbrace> \<lambda>Res sec' u.
               enc_sections_state_rel u data inst addr sec'
                 (flush_pending_outer_tail_state src_len s0 pending len
                   add_start loop_st) \<and>
               heap_typing u = heap_typing s0 \<rbrace>"
  shows "flush_pending_outer_emit_pre src_len s0 data data_cap inst inst_cap
          addr pending len spec_st add_start i sec_cur t"
  using run tail
  by (auto simp: flush_pending_outer_emit_pre_def)

lemma flush_pending_outer_loop_inv_start:
  assumes rel: "enc_sections_state_rel s data inst addr sec spec_st"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
  shows "flush_pending_outer_loop_inv src_len s data inst addr pending len
    spec_st 0 0 sec s"
  using rel sec_ok
  by (auto simp: flush_pending_outer_loop_inv_def)

lemma flush_pending_outer_loop_inv_short_step:
  assumes inv:
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start i sec_cur t"
      and i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and run_end:
        "pending_run_end (heap_bytes_word s0 pending 0 len) (unat i) =
         unat j"
      and short: "\<not> (4 :: 32 word) \<le> j - i"
  shows "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start j sec_cur t"
proof -
  obtain loop_st where
      add_start_le_i: "add_start \<le> i"
      and typing: "heap_typing t = heap_typing s0"
      and pending_frame:
        "heap_bytes_word t pending 0 len =
         heap_bytes_word s0 pending 0 len"
      and sec_ok: "sections_t_C.err_C sec_cur = ENC_OK"
      and rel: "enc_sections_state_rel t data inst addr sec_cur loop_st"
      and eq:
        "flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) (unat add_start) (unat i)
          loop_st =
         flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) 0 0 spec_st"
    using inv by (auto simp: flush_pending_outer_loop_inv_def)
  have add_start_le_j: "add_start \<le> j"
    using add_start_le_i i_lt_j by simp
  have step:
    "flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
      (unat add_start) (unat i) loop_st =
     flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
      (unat add_start) (unat j) loop_st"
    by (rule flush_pending_loop_spec_short_step_heap_word[
      OF i_lt_j j_le_len run_end short])
  show ?thesis
    unfolding flush_pending_outer_loop_inv_def
    apply (intro conjI)
        apply (rule add_start_le_j)
       apply (rule j_le_len)
      apply (rule typing)
     apply (rule pending_frame)
    apply (rule sec_ok)
    apply (intro exI[where x = loop_st] conjI)
     apply (rule rel)
    using step eq by simp
qed

lemma flush_pending_outer_loop_inv_run_step:
  assumes inv:
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start i sec_cur t"
      and i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and run_end:
        "pending_run_end (heap_bytes_word s0 pending 0 len) (unat i) =
         unat j"
      and run_ge: "(4 :: 32 word) \<le> j - i"
      and b_eq: "b = heap_w8 s0 (pending +\<^sub>p uint i)"
      and pending_frame:
        "heap_bytes_word u pending 0 len =
         heap_bytes_word s0 pending 0 len"
      and typing: "heap_typing u = heap_typing s0"
      and emitted:
        "\<And>loop_st. \<lbrakk>
          enc_sections_state_rel t data inst addr sec_cur loop_st;
          flush_pending_loop_spec src_len
            (heap_bytes_word s0 pending 0 len) (unat add_start) (unat i)
            loop_st =
          flush_pending_loop_spec src_len
            (heap_bytes_word s0 pending 0 len) 0 0 spec_st
        \<rbrakk> \<Longrightarrow>
          enc_sections_state_rel u data inst addr sec'
            (emit_inst_spec src_len (RRun b (unat (j - i)))
              (if add_start < i
               then emit_inst_spec src_len
                 (RAdd (heap_bytes_word s0 pending add_start
                   (i - add_start))) loop_st
               else loop_st))"
      and sec_ok: "sections_t_C.err_C sec' = ENC_OK"
  shows "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st j j sec' u"
proof -
  obtain loop_st where
      add_start_le_i: "add_start \<le> i"
      and rel: "enc_sections_state_rel t data inst addr sec_cur loop_st"
      and eq:
        "flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) (unat add_start) (unat i)
          loop_st =
         flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) 0 0 spec_st"
    using inv by (auto simp: flush_pending_outer_loop_inv_def)
  let ?loop_st' =
    "emit_inst_spec src_len (RRun b (unat (j - i)))
      (if add_start < i
       then emit_inst_spec src_len
         (RAdd (heap_bytes_word s0 pending add_start (i - add_start)))
         loop_st
       else loop_st)"
  have rel':
    "enc_sections_state_rel u data inst addr sec' ?loop_st'"
    by (rule emitted[OF rel eq])
  have step:
    "flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
      (unat add_start) (unat i) loop_st =
     flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
      (unat j) (unat j) ?loop_st'"
    by (rule flush_pending_loop_spec_run_step_heap_emit_word[
      OF add_start_le_i i_lt_j j_le_len run_end run_ge b_eq])
  show ?thesis
    unfolding flush_pending_outer_loop_inv_def
    apply (intro conjI)
        apply simp
       apply (rule j_le_len)
      apply (rule typing)
     apply (rule pending_frame)
    apply (rule sec_ok)
    apply (intro exI[where x = ?loop_st'] conjI)
     apply (rule rel')
    using step eq by simp
qed

lemma flush_pending_outer_after_scan_preserves_inv:
  assumes inv:
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start i sec_cur t"
      and i_lt_j: "i < j"
      and j_le_len: "j \<le> len"
      and run_end:
        "pending_run_end (heap_bytes_word s0 pending 0 len) (unat i) =
         unat j"
      and b_eq: "b = heap_w8 s0 (pending +\<^sub>p uint i)"
      and emit_pre:
        "flush_pending_outer_emit_pre src_len s0 data data_cap inst inst_cap
          addr pending len spec_st add_start i sec_cur t"
  shows "condition (\<lambda>st. (4 :: 32 word) \<le> j - i)
            (flush_pending_outer_run_branch data data_cap inst inst_cap
              pending add_start i j b sec_cur)
            (return (add_start, j, sec_cur)) \<bullet> t
         \<lbrace> \<lambda>r u.
              \<exists>add_start' i' sec_cur'.
                r = Result (add_start', i', sec_cur') \<and>
                i < i' \<and> i' \<le> len \<and>
                flush_pending_outer_loop_inv src_len s0 data inst addr
                  pending len spec_st add_start' i' sec_cur' u \<rbrace>"
proof (cases "(4 :: 32 word) \<le> j - i")
  case True
  obtain loop_st where
      add_start_le_i: "add_start \<le> i"
      and rel: "enc_sections_state_rel t data inst addr sec_cur loop_st"
      and eq:
        "flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) (unat add_start) (unat i)
          loop_st =
         flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) 0 0 spec_st"
    using inv by (auto simp: flush_pending_outer_loop_inv_def)
  have branch:
    "flush_pending_outer_run_branch data data_cap inst inst_cap pending
        add_start i j b sec_cur \<bullet> t
     \<lbrace> \<lambda>r u.
          \<exists>sec'.
            r = Result (j, j, sec') \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            heap_bytes_word u pending 0 len =
              heap_bytes_word s0 pending 0 len \<and>
            heap_typing u = heap_typing s0 \<and>
            enc_sections_state_rel u data inst addr sec'
              (flush_pending_outer_run_state src_len s0 pending
                add_start i j b loop_st) \<rbrace>"
    using emit_pre i_lt_j j_le_len run_end True b_eq rel eq
    by (auto simp: flush_pending_outer_emit_pre_def)
  show ?thesis
    using True
    apply simp
    apply (rule runs_to_weaken[OF branch])
    apply clarsimp
    subgoal for u sec'
    proof -
      assume sec_ok': "sections_t_C.err_C sec' = ENC_OK"
      assume pending_frame':
        "heap_bytes_word u pending 0 len =
         heap_bytes_word s0 pending 0 len"
      assume typing': "heap_typing u = heap_typing s0"
      assume rel':
        "enc_sections_state_rel u data inst addr sec'
          (flush_pending_outer_run_state src_len s0 pending
            add_start i j b loop_st)"
      have step:
        "flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) (unat add_start) (unat i)
          loop_st =
         flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) (unat j) (unat j)
          (flush_pending_outer_run_state src_len s0 pending
            add_start i j b loop_st)"
        unfolding flush_pending_outer_run_state_def
        by (rule flush_pending_loop_spec_run_step_heap_emit_word[
          OF add_start_le_i i_lt_j j_le_len run_end True b_eq])
      have inv':
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st j j sec' u"
        unfolding flush_pending_outer_loop_inv_def
        apply (intro conjI)
            apply simp
           apply (rule j_le_len)
          apply (rule typing')
         apply (rule pending_frame')
        apply (rule sec_ok')
        apply (intro exI[where x =
          "flush_pending_outer_run_state src_len s0 pending add_start i j b
            loop_st"] conjI)
         apply (rule rel')
        using step eq by simp
      show ?thesis
        using i_lt_j j_le_len inv' by auto
    qed
    done
next
  case False
  have inv':
    "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
      spec_st add_start j sec_cur t"
    by (rule flush_pending_outer_loop_inv_short_step[
      OF inv i_lt_j j_le_len run_end False])
  show ?thesis
    using False i_lt_j j_le_len inv'
    by simp
qed

lemma flush_pending_outer_scan_tail_preserves_inv:
  assumes inv:
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start i sec_cur t"
      and i_lt_len: "i < len"
      and b_eq_t: "b = heap_w8 t (pending +\<^sub>p uint i)"
      and pending_valid_t: "\<forall>j < unat len.
        ptr_valid (heap_typing t)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and emit_pre:
        "flush_pending_outer_emit_pre src_len s0 data data_cap inst inst_cap
          addr pending len spec_st add_start i sec_cur t"
  shows "(((do {
             ret \<leftarrow> liftE
               ((do {
                  x \<leftarrow> guard
                    (\<lambda>st. i + 1 < len \<longrightarrow>
                      IS_VALID(8 word) st (pending +\<^sub>p uint (i + 1)));
                  gets
                    (\<lambda>st. if i + 1 < len \<and>
                      heap_w8 st (pending +\<^sub>p uint (i + 1)) = b
                     then (1 :: int) else 0)
                }) :: (int, lifted_globals) res_monad);
             liftE
               ((whileLoop
                 (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
                 (\<lambda>(j, ret). do {
                    x \<leftarrow> guard
                      (\<lambda>st. j + 1 < len \<longrightarrow>
                        IS_VALID(8 word) st
                          (pending +\<^sub>p uint (j + 1)));
                    ret \<leftarrow> gets
                      (\<lambda>st. j + 1 < len \<and>
                        heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                    return (j + 1, if ret then 1 else 0)
                 })
                 (i + 1, ret)) :: (32 word \<times> int, lifted_globals) res_monad)
           }) :: (sections_t_C, 32 word \<times> int, lifted_globals) exn_monad) >>=
           (\<lambda>(j, ret). condition (\<lambda>st. (4 :: 32 word) \<le> j - i)
              (flush_pending_outer_run_branch data data_cap inst inst_cap
                pending add_start i j b sec_cur)
              (return (add_start, j, sec_cur)))) \<bullet> t
         \<lbrace> \<lambda>r u.
              \<exists>add_start' i' sec_cur'.
                r = Result (add_start', i', sec_cur') \<and>
                i < i' \<and> i' \<le> len \<and>
                flush_pending_outer_loop_inv src_len s0 data inst addr
                  pending len spec_st add_start' i' sec_cur' u \<rbrace>"
proof -
  obtain pending_frame where
      pending_frame:
        "heap_bytes_word t pending 0 len =
         heap_bytes_word s0 pending 0 len"
    using inv by (auto simp: flush_pending_outer_loop_inv_def)
  have b_eq_s0: "b = heap_w8 s0 (pending +\<^sub>p uint i)"
    using b_eq_t heap_bytes_word_frame_heap_w8_zero[
      OF pending_frame i_lt_len] by simp
  have scan:
    "((do {
        ret \<leftarrow> liftE
          ((do {
             x \<leftarrow> guard
               (\<lambda>st. i + 1 < len \<longrightarrow>
                 IS_VALID(8 word) st (pending +\<^sub>p uint (i + 1)));
             gets
               (\<lambda>st. if i + 1 < len \<and>
                 heap_w8 st (pending +\<^sub>p uint (i + 1)) = b
                then (1 :: int) else 0)
           }) :: (int, lifted_globals) res_monad);
        liftE
          ((whileLoop
            (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
            (\<lambda>(j, ret). do {
               x \<leftarrow> guard
                 (\<lambda>st. j + 1 < len \<longrightarrow>
                   IS_VALID(8 word) st
                     (pending +\<^sub>p uint (j + 1)));
               ret \<leftarrow> gets
                 (\<lambda>st. j + 1 < len \<and>
                   heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
               return (j + 1, if ret then 1 else 0)
            })
            (i + 1, ret)) :: (32 word \<times> int, lifted_globals) res_monad)
      }) :: (sections_t_C, 32 word \<times> int, lifted_globals) exn_monad) \<bullet> t
     \<lbrace> \<lambda>r u.
          \<exists>j. r = Result (j, 0) \<and> u = t \<and>
            i < j \<and> j \<le> len \<and>
            pending_run_end (heap_bytes_word s0 pending 0 len) (unat i) =
              unat j \<rbrace>"
    apply (rule runs_to_weaken[
      OF flush_pending'_scan_tail_from_liftE_split_pending_run_end[
        where s = t and pending = pending and len = len and i = i
          and b = b]])
       apply (rule i_lt_len)
      using b_eq_t apply simp
     apply (rule pending_valid_t)
    using pending_frame by auto
  show ?thesis
    apply (rule runs_to_bind_exception)
    apply (rule runs_to_weaken[OF scan])
    apply clarsimp
    subgoal for j
      by (rule flush_pending_outer_after_scan_preserves_inv[
        OF inv _ _ _ b_eq_s0 emit_pre]) auto
    done
qed

lemma flush_pending_outer_scan_tail_preserves_inv_do:
  assumes inv:
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start i sec_cur t"
      and i_lt_len: "i < len"
      and b_eq_t: "b = heap_w8 t (pending +\<^sub>p uint i)"
      and pending_valid_t: "\<forall>j < unat len.
        ptr_valid (heap_typing t)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and emit_pre:
        "flush_pending_outer_emit_pre src_len s0 data data_cap inst inst_cap
          addr pending len spec_st add_start i sec_cur t"
  shows "((do {
            ret \<leftarrow> liftE
              ((do {
                 x \<leftarrow> guard
                   (\<lambda>st. i + 1 < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint (i + 1)));
                 gets
                   (\<lambda>st. if i + 1 < len \<and>
                     heap_w8 st (pending +\<^sub>p uint (i + 1)) = b
                    then (1 :: int) else 0)
               }) :: (int, lifted_globals) res_monad);
            (j, ret) \<leftarrow> liftE
              ((whileLoop
                (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
                (\<lambda>(j, ret). do {
                   x \<leftarrow> guard
                     (\<lambda>st. j + 1 < len \<longrightarrow>
                       IS_VALID(8 word) st
                         (pending +\<^sub>p uint (j + 1)));
                   ret \<leftarrow> gets
                     (\<lambda>st. j + 1 < len \<and>
                       heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                   return (j + 1, if ret then 1 else 0)
                })
                (i + 1, ret)) :: (32 word \<times> int, lifted_globals) res_monad);
            condition (\<lambda>st. (4 :: 32 word) \<le> j - i)
              (flush_pending_outer_run_branch data data_cap inst inst_cap
                pending add_start i j b sec_cur)
              (return (add_start, j, sec_cur))
          }) :: (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
            lifted_globals) exn_monad) \<bullet> t
         \<lbrace> \<lambda>r u.
              \<exists>add_start' i' sec_cur'.
                r = Result (add_start', i', sec_cur') \<and>
                i < i' \<and> i' \<le> len \<and>
                flush_pending_outer_loop_inv src_len s0 data inst addr
                  pending len spec_st add_start' i' sec_cur' u \<rbrace>"
proof -
  show ?thesis
    using flush_pending_outer_scan_tail_preserves_inv[
      OF inv i_lt_len b_eq_t pending_valid_t emit_pre]
    by (simp add: bind_assoc)
qed

lemma flush_pending_outer_read_scan_tail_preserves_inv:
  assumes inv:
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start i sec_cur t"
      and i_lt_len: "i < len"
      and pending_valid_t: "\<forall>j < unat len.
        ptr_valid (heap_typing t)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and emit_pre:
        "flush_pending_outer_emit_pre src_len s0 data data_cap inst inst_cap
          addr pending len spec_st add_start i sec_cur t"
  shows "((do {
            b \<leftarrow> gets (\<lambda>st. heap_w8 st (pending +\<^sub>p uint i));
            ret \<leftarrow> liftE
              ((do {
                 x \<leftarrow> guard
                   (\<lambda>st. i + 1 < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint (i + 1)));
                 gets
                   (\<lambda>st. if i + 1 < len \<and>
                     heap_w8 st (pending +\<^sub>p uint (i + 1)) = b
                    then (1 :: int) else 0)
               }) :: (int, lifted_globals) res_monad);
            (j, ret) \<leftarrow> liftE
              ((whileLoop
                (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
                (\<lambda>(j, ret). do {
                   x \<leftarrow> guard
                     (\<lambda>st. j + 1 < len \<longrightarrow>
                       IS_VALID(8 word) st
                         (pending +\<^sub>p uint (j + 1)));
                   ret \<leftarrow> gets
                     (\<lambda>st. j + 1 < len \<and>
                       heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                   return (j + 1, if ret then 1 else 0)
                })
                (i + 1, ret)) :: (32 word \<times> int, lifted_globals) res_monad);
            condition (\<lambda>st. (4 :: 32 word) \<le> j - i)
              (flush_pending_outer_run_branch data data_cap inst inst_cap
                pending add_start i j b sec_cur)
              (return (add_start, j, sec_cur))
          }) :: (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
            lifted_globals) exn_monad) \<bullet> t
         \<lbrace> \<lambda>r u.
              \<exists>add_start' i' sec_cur'.
                r = Result (add_start', i', sec_cur') \<and>
                i < i' \<and> i' \<le> len \<and>
                flush_pending_outer_loop_inv src_len s0 data inst addr
                  pending len spec_st add_start' i' sec_cur' u \<rbrace>"
proof -
  have get_b:
    "((gets (\<lambda>st. heap_w8 st (pending +\<^sub>p uint i))) ::
       (sections_t_C, 8 word, lifted_globals) exn_monad) \<bullet> t
     \<lbrace> \<lambda>r u. r = Result (heap_w8 t (pending +\<^sub>p uint i)) \<and> u = t \<rbrace>"
    by runs_to_vcg
  show ?thesis
  apply (rule runs_to_bind_exception)
   apply (rule runs_to_weaken[OF get_b])
   apply clarsimp
   apply (rule flush_pending_outer_scan_tail_preserves_inv_do[
     OF inv i_lt_len _ pending_valid_t emit_pre])
   apply simp
  done
qed

lemma flush_pending_outer_body_preserves_inv:
  assumes inv:
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start i sec_cur t"
      and i_lt_len: "i < len"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s0)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and emit_pre:
        "flush_pending_outer_emit_pre src_len s0 data data_cap inst inst_cap
          addr pending len spec_st add_start i sec_cur t"
  shows "flush_pending_outer_body data data_cap inst inst_cap pending len
            (add_start, i, sec_cur) \<bullet> t
         \<lbrace> \<lambda>r u.
              \<exists>add_start' i' sec_cur'.
                r = Result (add_start', i', sec_cur') \<and>
                i < i' \<and> i' \<le> len \<and>
                flush_pending_outer_loop_inv src_len s0 data inst addr
                  pending len spec_st add_start' i' sec_cur' u \<rbrace>"
proof -
  have typing: "heap_typing t = heap_typing s0"
    using inv by (simp add: flush_pending_outer_loop_inv_def)
  have pending_valid_t:
    "\<forall>j < unat len.
      ptr_valid (heap_typing t)
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
    using pending_valid typing by simp
  have guard_i:
    "((guard (\<lambda>st. IS_VALID(8 word) st (pending +\<^sub>p uint i))) ::
       (sections_t_C, unit, lifted_globals) exn_monad) \<bullet> t
     \<lbrace> \<lambda>r u. r = Result () \<and> u = t \<rbrace>"
    apply runs_to_vcg
    using pending_valid_t[rule_format, of "unat i"] i_lt_len
    by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
  show ?thesis
    unfolding flush_pending_outer_body_def
    apply simp
    apply (rule runs_to_bind_exception)
    apply (rule runs_to_weaken[OF guard_i])
    apply clarsimp
    apply (rule flush_pending_outer_read_scan_tail_preserves_inv[
      OF inv i_lt_len pending_valid_t emit_pre])
    done
qed

lemma unat_diff_measure_decrease_word:
  fixes i i' len :: "32 word"
  assumes i_lt_i': "i < i'"
      and i'_le_len: "i' \<le> len"
  shows "unat len - unat i' < unat len - unat i"
proof -
  have "unat i < unat i'"
    using i_lt_i' by (simp add: word_less_nat_alt)
  moreover have "unat i' \<le> unat len"
    using i'_le_len by (simp add: word_le_nat_alt)
  ultimately show ?thesis
    by linarith
qed

lemma flush_pending_outer_loop_preserves_inv:
  assumes inv0:
        "flush_pending_outer_loop_inv src_len s data inst addr pending len
          spec_st 0 0 sec s"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and emit_pre:
        "\<And>add_start i sec_cur t. \<lbrakk>
          flush_pending_outer_loop_inv src_len s data inst addr pending len
            spec_st add_start i sec_cur t;
          i < len
        \<rbrakk> \<Longrightarrow>
          flush_pending_outer_emit_pre src_len s data data_cap inst inst_cap
            addr pending len spec_st add_start i sec_cur t"
  shows "(whileLoop
           (\<lambda>(add_start :: 32 word, i :: 32 word,
                sec_cur :: sections_t_C) st. i < len)
           (flush_pending_outer_body data data_cap inst inst_cap pending len)
           (0, 0, sec) ::
             (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
               lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              \<exists>add_start sec'.
                r = Result (add_start, len, sec') \<and>
                flush_pending_outer_loop_inv src_len s data inst addr
                  pending len spec_st add_start len sec' t \<rbrace>"
  apply (rule runs_to_whileLoop_exn'[
    where R = "measure
      (\<lambda>((add_start :: 32 word, i :: 32 word,
            sec_cur :: sections_t_C), _). unat len - unat i)"
      and I = "\<lambda>r t.
        ((\<exists>add_start i sec_cur.
            r = Result (add_start, i, sec_cur) \<and>
            flush_pending_outer_loop_inv src_len s data inst addr pending len
              spec_st add_start i sec_cur t) \<and>
         (\<forall>e. r = Exn e \<longrightarrow> False))"])
  subgoal for a t
    apply (cases a)
    apply clarsimp
    subgoal for add_start i sec_cur
      apply (rule runs_to_weaken)
       apply (rule flush_pending_outer_body_preserves_inv)
          apply assumption
         apply assumption
        apply (rule pending_valid)
       apply (rule emit_pre)
        apply assumption
       apply assumption
      apply clarsimp
      apply (rule unat_diff_measure_decrease_word)
       apply assumption
      apply assumption
    done
  done
  subgoal for a t
    apply (cases a)
    apply clarsimp
    subgoal premises prems for add_start i sec_cur
    proof -
      have i_eq: "i = len"
        using prems by (auto simp: flush_pending_outer_loop_inv_def)
      show ?thesis
        using prems i_eq by auto
    qed
    done
  subgoal by auto
  subgoal by simp
  subgoal using inv0 by auto
  done

lemma flush_pending_outer_tail_finishes_inv:
  assumes inv:
        "flush_pending_outer_loop_inv src_len s0 data inst addr pending len
          spec_st add_start len sec_cur t"
      and emit_pre:
        "flush_pending_outer_emit_pre src_len s0 data data_cap inst inst_cap
          addr pending len spec_st add_start len sec_cur t"
  shows "flush_pending_outer_tail data data_cap inst inst_cap pending len
            add_start sec_cur \<bullet> t
         \<lbrace> \<lambda>Res sec' u.
              enc_sections_state_rel u data inst addr sec'
                (flush_pending_loop_spec src_len
                  (heap_bytes_word s0 pending 0 len) 0 0 spec_st) \<and>
              heap_typing u = heap_typing s0 \<rbrace>"
proof -
  obtain loop_st where
      add_start_le_len: "add_start \<le> len"
      and rel: "enc_sections_state_rel t data inst addr sec_cur loop_st"
      and eq:
        "flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) (unat add_start) (unat len)
          loop_st =
         flush_pending_loop_spec src_len
          (heap_bytes_word s0 pending 0 len) 0 0 spec_st"
    using inv by (auto simp: flush_pending_outer_loop_inv_def)
  have tail:
    "flush_pending_outer_tail data data_cap inst inst_cap pending len
        add_start sec_cur \<bullet> t
     \<lbrace> \<lambda>Res sec' u.
          enc_sections_state_rel u data inst addr sec'
            (flush_pending_outer_tail_state src_len s0 pending len
              add_start loop_st) \<and>
          heap_typing u = heap_typing s0 \<rbrace>"
    using emit_pre rel eq
    by (auto simp: flush_pending_outer_emit_pre_def)
  have exit:
    "flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
      (unat add_start) (unat len) loop_st =
     flush_pending_outer_tail_state src_len s0 pending len add_start
       loop_st"
    unfolding flush_pending_outer_tail_state_def
    by (rule flush_pending_loop_spec_exit_heap_emit_word[
      OF add_start_le_len]) simp
  have tail_state_eq:
    "flush_pending_outer_tail_state src_len s0 pending len add_start
       loop_st =
     flush_pending_loop_spec src_len (heap_bytes_word s0 pending 0 len)
       0 0 spec_st"
    using exit eq by simp
  show ?thesis
    apply (rule runs_to_weaken[OF tail])
    using tail_state_eq by auto
qed

lemma flush_pending'_enc_sections_state_rel_loop_spec_topdown:
  assumes rel: "enc_sections_state_rel s data inst addr sec spec_st"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and emit_pre:
        "\<And>add_start i sec_cur t. \<lbrakk>
          flush_pending_outer_loop_inv src_len s data inst addr pending len
            spec_st add_start i sec_cur t;
          i \<le> len
        \<rbrakk> \<Longrightarrow>
          flush_pending_outer_emit_pre src_len s data data_cap inst inst_cap
            addr pending len spec_st add_start i sec_cur t"
  shows "flush_pending' sec data data_cap inst inst_cap pending len \<bullet> s
         \<lbrace> \<lambda>r t.
              \<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_loop_spec src_len
                    (heap_bytes_word s pending 0 len) 0 0 spec_st) \<and>
                heap_typing t = heap_typing s \<rbrace>"
proof -
  have inv0:
    "flush_pending_outer_loop_inv src_len s data inst addr pending len
      spec_st 0 0 sec s"
    by (rule flush_pending_outer_loop_inv_start[OF rel sec_ok])
  have loop:
    "(whileLoop
       (\<lambda>(add_start :: 32 word, i :: 32 word,
            sec_cur :: sections_t_C) st. i < len)
       (flush_pending_outer_body data data_cap inst inst_cap pending len)
       (0, 0, sec) ::
         (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
           lifted_globals) exn_monad) \<bullet> s
     \<lbrace> \<lambda>r t.
          \<exists>add_start sec'.
            r = Result (add_start, len, sec') \<and>
            flush_pending_outer_loop_inv src_len s data inst addr
              pending len spec_st add_start len sec' t \<rbrace>"
    by (rule flush_pending_outer_loop_preserves_inv[OF inv0 pending_valid])
       (auto intro: emit_pre)
  show ?thesis
    unfolding flush_pending'_def flush_pending_outer_body_def
      flush_pending_outer_run_branch_def
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF loop[
      unfolded flush_pending_outer_body_def
        flush_pending_outer_run_branch_def]])
    subgoal premises loop_post for r t
    proof -
      obtain add_start sec' where
          r_def: "r = Result (add_start, len, sec')"
        and inv:
          "flush_pending_outer_loop_inv src_len s data inst addr pending len
            spec_st add_start len sec' t"
        using loop_post by auto
      have tail:
        "flush_pending_outer_tail data data_cap inst inst_cap pending len
            add_start sec' \<bullet> t
         \<lbrace> \<lambda>Res sec'' u.
              enc_sections_state_rel u data inst addr sec''
                (flush_pending_loop_spec src_len
                  (heap_bytes_word s pending 0 len) 0 0 spec_st) \<and>
              heap_typing u = heap_typing s \<rbrace>"
        by (rule flush_pending_outer_tail_finishes_inv[OF inv])
           (rule emit_pre[OF inv order_refl])
      show ?thesis
        apply (simp add: r_def)
        apply (rule runs_to_weaken[
          OF runs_to_liftE_bind_throw_result[
            OF tail[unfolded flush_pending_outer_tail_def],
            where Q = "\<lambda>sec'' u.
              enc_sections_state_rel u data inst addr sec''
                (flush_pending_loop_spec src_len
                  (heap_bytes_word s pending 0 len) 0 0 spec_st) \<and>
              heap_typing u = heap_typing s"]])
        apply auto
        done
    qed
    done
qed

lemma flush_pending'_enc_sections_state_rel_topdown:
  assumes rel: "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq: "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and emit_pre:
        "\<And>add_start i sec_cur t. \<lbrakk>
          flush_pending_outer_loop_inv src_len s data inst addr pending len
            spec_st add_start i sec_cur t;
          i \<le> len
        \<rbrakk> \<Longrightarrow>
          flush_pending_outer_emit_pre src_len s data data_cap inst inst_cap
            addr pending len spec_st add_start i sec_cur t"
  shows "flush_pending' sec data data_cap inst inst_cap pending len \<bullet> s
         \<lbrace> \<lambda>r t.
              \<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st) \<and>
                heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF flush_pending'_enc_sections_state_rel_loop_spec_topdown[
      OF rel sec_ok pending_valid emit_pre]])
  using flush_pending_loop_spec_eq_flush_pending_spec[OF pending_eq]
  by auto

lemma flush_pending'_enc_sections_state_rel_branch_pre:
  assumes rel: "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq: "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and run_pre:
        "\<And>add_start i sec_cur t j b loop_st. \<lbrakk>
          flush_pending_outer_loop_inv src_len s data inst addr pending len
            spec_st add_start i sec_cur t;
          i \<le> len;
          i < j;
          j \<le> len;
          pending_run_end (heap_bytes_word s pending 0 len) (unat i) =
            unat j;
          (4 :: 32 word) \<le> j - i;
          b = heap_w8 s (pending +\<^sub>p uint i);
          enc_sections_state_rel t data inst addr sec_cur loop_st;
          flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
            (unat add_start) (unat i) loop_st =
          flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
            0 0 spec_st
        \<rbrakk> \<Longrightarrow>
          flush_pending_outer_run_branch data data_cap inst inst_cap pending
            add_start i j b sec_cur \<bullet> t
          \<lbrace> \<lambda>r u.
               \<exists>sec'.
                 r = Result (j, j, sec') \<and>
                 sections_t_C.err_C sec' = ENC_OK \<and>
                 heap_bytes_word u pending 0 len =
                   heap_bytes_word s pending 0 len \<and>
                 heap_typing u = heap_typing s \<and>
                 enc_sections_state_rel u data inst addr sec'
                   (flush_pending_outer_run_state src_len s pending
                     add_start i j b loop_st) \<rbrace>"
      and tail_pre:
        "\<And>add_start i sec_cur t loop_st. \<lbrakk>
          flush_pending_outer_loop_inv src_len s data inst addr pending len
            spec_st add_start i sec_cur t;
          i \<le> len;
          i = len;
          enc_sections_state_rel t data inst addr sec_cur loop_st;
          flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
            (unat add_start) (unat len) loop_st =
          flush_pending_loop_spec src_len (heap_bytes_word s pending 0 len)
            0 0 spec_st
        \<rbrakk> \<Longrightarrow>
          flush_pending_outer_tail data data_cap inst inst_cap pending len
            add_start sec_cur \<bullet> t
          \<lbrace> \<lambda>Res sec' u.
               enc_sections_state_rel u data inst addr sec'
                 (flush_pending_outer_tail_state src_len s pending len
                   add_start loop_st) \<and>
               heap_typing u = heap_typing s \<rbrace>"
  shows "flush_pending' sec data data_cap inst inst_cap pending len \<bullet> s
         \<lbrace> \<lambda>r t.
              \<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st) \<and>
                heap_typing t = heap_typing s \<rbrace>"
  apply (rule flush_pending'_enc_sections_state_rel_topdown[
    OF rel pending_eq sec_ok pending_valid])
  subgoal for add_start i sec_cur t
    apply (rule flush_pending_outer_emit_preI)
     subgoal for j b loop_st
       by (rule run_pre) auto
    subgoal for loop_st
      by (rule tail_pre) auto
    done
  done

lemma flush_pending'_replicate_run_inner_loop_from_exn:
  fixes len start :: "32 word"
  assumes start_lt: "start < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                  heap_w8 s pending);
              return (j + 1, if ret then 1 else 0)
           }) (start, 1) :: ('e, 32 word \<times> 32 word, lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_whileLoop_exn'[
    where R = "measure
      (\<lambda>((j :: 32 word, ret :: 32 word), _). unat len - unat j)"
      and I = "\<lambda>r t.
        ((\<forall>j ret. r = Result (j, ret) \<longrightarrow>
            unat j \<le> unat len \<and>
            (ret \<noteq> 0 \<longleftrightarrow> j < len) \<and>
            t = s) \<and>
         (\<forall>e. r = Exn e \<longrightarrow> False))"])
  subgoal for a t
    apply (cases a)
    apply clarsimp
    subgoal for j ret
      apply runs_to_vcg
      subgoal
        using pending_valid[rule_format, of "unat (j + 1)"]
        by (simp add: word_less_nat_alt word_unat.Rep_inverse)
      subgoal
        by (rule unat_suc_le_of_word_less)
      subgoal
        using unat_measure_decrease_of_unat_less32[of j len]
        by (simp add: word_less_nat_alt)
      subgoal
        using pending_all_eq[rule_format, of "unat (j + 1)"]
        by (auto simp: word_less_nat_alt word_unat.Rep_inverse
                 intro: word_suc_eq_of_unat_lt_not_unat_suc_lt32
                        unat_suc_le_of_unat_less32)
      subgoal
        using pending_all_eq[rule_format, of "unat (j + 1)"]
        by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
      subgoal
        using unat_measure_decrease_of_unat_less32[of j len]
        by (simp add: word_less_nat_alt)
      done
    done
  subgoal premises prems for a t
  proof -
    obtain j ret where a_def: "a = (j, ret)"
      by (cases a)
    have j_le: "unat j \<le> unat len"
      using prems a_def by auto
    have not_lt: "\<not> j < len"
      using prems a_def by auto
    have "unat len \<le> unat j"
      using not_lt by (simp add: word_less_nat_alt)
    then have j_eq: "j = len"
      using j_le by (metis antisym_conv word_unat.Rep_inject)
    have ret_eq: "ret = 0"
      using prems a_def by auto
    show ?thesis
      using prems a_def j_eq ret_eq by simp
  qed
  subgoal by simp
  subgoal by simp
  subgoal using start_lt by (auto simp: word_less_nat_alt)
  done

lemma flush_pending'_replicate_run_prescan_two_Res:
  fixes len :: "32 word"
  assumes len_gt2: "(2 :: 32 word) < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "((do {
              x \<leftarrow> guard
                (\<lambda>st. (2 :: 32 word) < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (2 :: 32 word)));
              ret \<leftarrow> gets
                (\<lambda>st. (2 :: 32 word) < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (2 :: 32 word)) =
                  heap_w8 s pending);
              return ((2 :: 32 word), if ret then 1 else 0)
            } >>= whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
              (\<lambda>(j, ret). do {
                 x \<leftarrow> guard
                   (\<lambda>st. j + 1 < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
                 ret \<leftarrow> gets
                   (\<lambda>st. j + 1 < len \<and>
                     heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                     heap_w8 s pending);
                 return (j + 1, if ret then 1 else 0)
              })) :: (32 word \<times> 32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t. r = (len, 0) \<and> t = s \<rbrace>"
proof -
  have v2:
    "ptr_valid (heap_typing s) (pending +\<^sub>p uint (2 :: 32 word))"
    using pending_valid[rule_format, of 2] len_gt2
    by (simp add: word_less_nat_alt)
  have p2:
    "heap_w8 s (pending +\<^sub>p uint (2 :: 32 word)) =
      heap_w8 s pending"
    using pending_all_eq[rule_format, of 2] len_gt2
    by (auto simp: word_less_nat_alt)
  show ?thesis
    apply runs_to_vcg
    using v2 apply simp
    using p2 len_gt2 apply simp
    apply (rule runs_to_weaken[
      OF flush_pending'_replicate_run_inner_loop_from_Res])
       apply (rule len_gt2)
      apply (rule pending_all_eq)
     apply (rule pending_valid)
    using len_gt2 p2 by auto
qed

lemma flush_pending'_replicate_run_prescan_two_liftE:
  fixes len :: "32 word"
  assumes len_gt2: "(2 :: 32 word) < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(liftE
           ((do {
              x \<leftarrow> guard
                (\<lambda>st. (2 :: 32 word) < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (2 :: 32 word)));
              ret \<leftarrow> gets
                (\<lambda>st. (2 :: 32 word) < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (2 :: 32 word)) =
                  heap_w8 s pending);
              return ((2 :: 32 word), if ret then 1 else 0)
            } >>= whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
              (\<lambda>(j, ret). do {
                 x \<leftarrow> guard
                   (\<lambda>st. j + 1 < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
                 ret \<leftarrow> gets
                   (\<lambda>st. j + 1 < len \<and>
                     heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                     heap_w8 s pending);
                 return (j + 1, if ret then 1 else 0)
              })) :: (32 word \<times> 32 word, lifted_globals) res_monad)
          :: ('e, 32 word \<times> 32 word, lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_liftE)
  apply (rule runs_to_weaken[
    OF flush_pending'_replicate_run_prescan_two_Res])
    apply (rule len_gt2)
   apply (rule pending_all_eq)
  apply (rule pending_valid)
  by auto

lemma flush_pending'_replicate_run_prescan_two_condition_liftE:
  fixes len :: "32 word"
  assumes len_gt2: "(2 :: 32 word) < len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(liftE
           (condition (\<lambda>st. True)
             ((do {
                x \<leftarrow> guard
                  (\<lambda>st. (2 :: 32 word) < len \<longrightarrow>
                    IS_VALID(8 word) st (pending +\<^sub>p 2));
                ret \<leftarrow> gets
                  (\<lambda>st. (2 :: 32 word) < len \<and>
                    heap_w8 st (pending +\<^sub>p 2) =
                    heap_w8 s pending);
                return ((2 :: 32 word), if ret then 1 else 0)
              } >>= whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
                (\<lambda>(j, ret). do {
                   x \<leftarrow> guard
                     (\<lambda>st. j + 1 < len \<longrightarrow>
                       IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
                   ret \<leftarrow> gets
                     (\<lambda>st. j + 1 < len \<and>
                       heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                       heap_w8 s pending);
                   return (j + 1, if ret then 1 else 0)
                })) :: (32 word \<times> 32 word, lifted_globals) res_monad)
             (return ((1 :: 32 word), 1 :: 32 word)))
          :: ('e, 32 word \<times> 32 word, lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_liftE)
  apply (simp add: condition_def)
  by (rule flush_pending'_replicate_run_prescan_two_Res[
      OF len_gt2 pending_all_eq pending_valid, simplified])

lemma flush_pending'_replicate_run_tail_after_first_ret_enc_sections_state_rel:
  fixes len :: "32 word"
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' len s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "((do {
            (j, ret) \<leftarrow> liftE
              (condition (\<lambda>st. True)
                ((do {
                   x \<leftarrow> guard
                     (\<lambda>st. (2 :: 32 word) < len \<longrightarrow>
                       IS_VALID(8 word) st (pending +\<^sub>p 2));
                   ret \<leftarrow> gets
                     (\<lambda>st. (2 :: 32 word) < len \<and>
                       heap_w8 st (pending +\<^sub>p 2) =
                       heap_w8 s pending);
                   return ((2 :: 32 word), if ret then 1 else 0)
                 } >>= whileLoop
                   (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
                   (\<lambda>(j, ret). do {
                      x \<leftarrow> guard
                        (\<lambda>st. j + 1 < len \<longrightarrow>
                          IS_VALID(8 word) st
                            (pending +\<^sub>p uint (j + 1)));
                      ret \<leftarrow> gets
                        (\<lambda>st. j + 1 < len \<and>
                          heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                          heap_w8 s pending);
                      return (j + 1, if ret then 1 else 0)
                   })) :: (32 word \<times> 32 word, lifted_globals) res_monad)
                (return ((1 :: 32 word), 1 :: 32 word)));
            condition (\<lambda>st. (4 :: 32 word) \<le> j - 0)
              (do {
                 sec_cur \<leftarrow> condition (\<lambda>st. (0 :: 32 word) < 0)
                   (do {
                      sec_cur \<leftarrow> liftE
                        (emit_add' sec data data_cap inst inst_cap
                          pending 0 (0 - 0));
                      unless (sections_t_C.err_C sec_cur = ENC_OK)
                        (throw sec_cur);
                      return sec_cur
                   })
                   (return sec);
                 sec_cur \<leftarrow> liftE
                   (emit_run' sec_cur data data_cap inst inst_cap
                     (heap_w8 s pending) (j - 0));
                 unless (sections_t_C.err_C sec_cur = ENC_OK)
                   (throw sec_cur);
                 return (j, j, sec_cur)
              })
              (return (0, j, sec))
          }) :: (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
                   lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              (\<exists>sec'. r = Result (len, len, sec') \<and>
                 enc_sections_state_rel t data inst addr sec'
                   (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?fill = "heap_w8 s pending"
  have len_gt2: "(2 :: 32 word) < len"
    using len_ge by (simp add: word_less_nat_alt word_le_nat_alt)
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    by (rule flush_pending_spec_heap_all_eq_run_sections[
        OF pending_eq len_ge pending_all_eq])+
  have size_unique:
    "\<And>n'. varint_size' len s = Some n' \<Longrightarrow> n' = n"
    using size by simp
  show ?thesis
    apply (rule runs_to_bind_exception)
    apply (rule runs_to_weaken[
      OF flush_pending'_replicate_run_prescan_two_condition_liftE[
        OF len_gt2 pending_all_eq pending_valid]])
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken)
     apply (rule emit_pending_run_chunk_enc_sections_state_rel[
        where src_len = src_len])
                    apply (rule rel)
                   apply (rule sec_ok)
                  apply (rule inst_byte_fits)
                 apply (rule inst_byte_ptr)
                apply (rule inst_byte_dist)
               apply (rule inst_byte_data_disj)
              apply (rule inst_byte_addr_disj)
             using size_unique inst_varint_fits apply blast
            using size_unique inst_varint_valid apply blast
           using size_unique inst_varint_inj apply blast
          using size_unique inst_varint_prefix_disj apply blast
         using size_unique inst_varint_no_overflow apply blast
        using size_unique inst_varint_data_disj apply blast
       using size_unique inst_varint_addr_disj apply blast
      apply (rule data_byte_fits)
     apply (rule data_byte_ptr)
    apply (rule data_byte_dist)
    using size_unique data_byte_inst_disj apply blast
    apply (rule data_byte_addr_disj)
    using pure_sections len_ge
    apply (auto simp: enc_sections_state_rel_def
                      sections_result_def word_le_nat_alt)
    done
qed

lemma flush_pending'_replicate_run_outer_body_start_enc_sections_state_rel:
  fixes len :: "32 word"
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' len s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "((do {
            guard (\<lambda>st. IS_VALID(8 word) st pending);
            b \<leftarrow> gets (\<lambda>st. heap_w8 st pending);
            ret \<leftarrow> liftE
              ((do {
                 guard
                   (\<lambda>st. (1 :: 32 word) < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p 1));
                 gets
                   (\<lambda>st. if (1 :: 32 word) < len \<and>
                     heap_w8 st (pending +\<^sub>p 1) = b
                    then 1 else 0)
               }) :: (32 word, lifted_globals) res_monad);
            (j, ret) \<leftarrow> liftE
              (condition (\<lambda>st. ret \<noteq> 0)
                ((do {
                   x \<leftarrow> guard
                     (\<lambda>st. (2 :: 32 word) < len \<longrightarrow>
                       IS_VALID(8 word) st (pending +\<^sub>p 2));
                   ret \<leftarrow> gets
                     (\<lambda>st. (2 :: 32 word) < len \<and>
                       heap_w8 st (pending +\<^sub>p 2) = b);
                   return ((2 :: 32 word), if ret then 1 else 0)
                 } >>= whileLoop
                   (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
                   (\<lambda>(j, ret). do {
                      x \<leftarrow> guard
                        (\<lambda>st. j + 1 < len \<longrightarrow>
                          IS_VALID(8 word) st
                            (pending +\<^sub>p uint (j + 1)));
                      ret \<leftarrow> gets
                        (\<lambda>st. j + 1 < len \<and>
                          heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                      return (j + 1, if ret then 1 else 0)
                   })) :: (32 word \<times> 32 word, lifted_globals) res_monad)
                (return ((1 :: 32 word), ret)));
            condition (\<lambda>st. (4 :: 32 word) \<le> j - 0)
              (do {
                 sec_cur \<leftarrow> condition (\<lambda>st. (0 :: 32 word) < 0)
                   (do {
                      sec_cur \<leftarrow> liftE
                        (emit_add' sec data data_cap inst inst_cap
                          pending 0 (0 - 0));
                      unless (sections_t_C.err_C sec_cur = ENC_OK)
                        (throw sec_cur);
                      return sec_cur
                   })
                   (return sec);
                 sec_cur \<leftarrow> liftE
                   (emit_run' sec_cur data data_cap inst inst_cap
                     b (j - 0));
                 unless (sections_t_C.err_C sec_cur = ENC_OK)
                   (throw sec_cur);
                 return (j, j, sec_cur)
              })
              (return (0, j, sec))
          }) :: (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
                   lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              (\<exists>sec'. r = Result (len, len, sec') \<and>
                 enc_sections_state_rel t data inst addr sec'
                   (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have len_gt1: "(1 :: 32 word) < len"
    using len_ge by (simp add: word_less_nat_alt word_le_nat_alt)
  have len_gt2: "(2 :: 32 word) < len"
    using len_ge by (simp add: word_less_nat_alt word_le_nat_alt)
  have v0: "ptr_valid (heap_typing s) pending"
    using pending_valid[rule_format, of 0] len_ge
    by (simp add: word_le_nat_alt)
  have v1: "ptr_valid (heap_typing s) (pending +\<^sub>p 1)"
    using pending_valid[rule_format, of 1] len_ge
    by (simp add: word_le_nat_alt)
  have v2: "ptr_valid (heap_typing s) (pending +\<^sub>p 2)"
    using pending_valid[rule_format, of 2] len_gt2
    by (simp add: word_less_nat_alt uint_numeral)
  have p1: "heap_w8 s (pending +\<^sub>p 1) = heap_w8 s pending"
    using pending_all_eq[rule_format, of 1] len_ge
    by (simp add: word_le_nat_alt)
  have p2: "heap_w8 s (pending +\<^sub>p 2) = heap_w8 s pending"
    using pending_all_eq[rule_format, of 2] len_ge
    by (simp add: word_less_nat_alt word_le_nat_alt)
  let ?fill = "heap_w8 s pending"
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    by (rule flush_pending_spec_heap_all_eq_run_sections[
        OF pending_eq len_ge pending_all_eq])+
  have size_unique:
    "\<And>n'. varint_size' len s = Some n' \<Longrightarrow> n' = n"
    using size by simp
  show ?thesis
    apply runs_to_vcg
    subgoal using v0 by simp
    subgoal using v1 by simp
    subgoal using v2 by simp
    subgoal
      apply (rule runs_to_weaken[
        OF flush_pending'_replicate_run_inner_loop_from_Res])
         apply (rule len_gt2)
        apply (rule pending_all_eq)
       apply (rule pending_valid)
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken)
       apply (rule emit_pending_run_chunk_enc_sections_state_rel[
          where src_len = src_len])
                      apply (rule rel)
                     apply (rule sec_ok)
                    apply (rule inst_byte_fits)
                   apply (rule inst_byte_ptr)
                  apply (rule inst_byte_dist)
                 apply (rule inst_byte_data_disj)
                apply (rule inst_byte_addr_disj)
               using size_unique inst_varint_fits apply blast
              using size_unique inst_varint_valid apply blast
             using size_unique inst_varint_inj apply blast
            using size_unique inst_varint_prefix_disj apply blast
           using size_unique inst_varint_no_overflow apply blast
          using size_unique inst_varint_data_disj apply blast
         using size_unique inst_varint_addr_disj apply blast
        apply (rule data_byte_fits)
       apply (rule data_byte_ptr)
      apply (rule data_byte_dist)
      using size_unique data_byte_inst_disj apply blast
      apply (rule data_byte_addr_disj)
      using pure_sections len_ge
      apply (auto simp: enc_sections_state_rel_def
                        sections_result_def word_le_nat_alt)
      done
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    done
qed

lemma flush_pending'_replicate_run_outer_body_start_enc_sections_state_rel_int:
  fixes len :: "32 word"
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' len s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "((do {
            guard (\<lambda>st. IS_VALID(8 word) st pending);
            b \<leftarrow> gets (\<lambda>st. heap_w8 st pending);
            ret \<leftarrow> liftE
              ((do {
                 guard
                   (\<lambda>st. (1 :: 32 word) < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p 1));
                 gets
                   (\<lambda>st. if (1 :: 32 word) < len \<and>
                     heap_w8 st (pending +\<^sub>p 1) = b
                    then 1 else 0)
               }) :: (int, lifted_globals) res_monad);
            (j, ret) \<leftarrow> liftE
              (condition (\<lambda>st. ret \<noteq> 0)
                ((do {
                   x \<leftarrow> guard
                     (\<lambda>st. (2 :: 32 word) < len \<longrightarrow>
                       IS_VALID(8 word) st (pending +\<^sub>p 2));
                   ret \<leftarrow> gets
                     (\<lambda>st. (2 :: 32 word) < len \<and>
                       heap_w8 st (pending +\<^sub>p 2) = b);
                   return ((2 :: 32 word), if ret then 1 else 0)
                 } >>= whileLoop
                   (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
                   (\<lambda>(j, ret). do {
                      x \<leftarrow> guard
                        (\<lambda>st. j + 1 < len \<longrightarrow>
                          IS_VALID(8 word) st
                            (pending +\<^sub>p uint (j + 1)));
                      ret \<leftarrow> gets
                        (\<lambda>st. j + 1 < len \<and>
                          heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                      return (j + 1, if ret then 1 else 0)
                   })) :: (32 word \<times> int, lifted_globals) res_monad)
                (return ((1 :: 32 word), ret)));
            condition (\<lambda>st. (4 :: 32 word) \<le> j - 0)
              (do {
                 sec_cur \<leftarrow> condition (\<lambda>st. (0 :: 32 word) < 0)
                   (do {
                      sec_cur \<leftarrow> liftE
                        (emit_add' sec data data_cap inst inst_cap
                          pending 0 (0 - 0));
                      unless (sections_t_C.err_C sec_cur = ENC_OK)
                        (throw sec_cur);
                      return sec_cur
                   })
                   (return sec);
                 sec_cur \<leftarrow> liftE
                   (emit_run' sec_cur data data_cap inst inst_cap
                     b (j - 0));
                 unless (sections_t_C.err_C sec_cur = ENC_OK)
                   (throw sec_cur);
                 return (j, j, sec_cur)
              })
              (return (0, j, sec))
          }) :: (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
                   lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              (\<exists>sec'. r = Result (len, len, sec') \<and>
                 enc_sections_state_rel t data inst addr sec'
                   (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have len_gt1: "(1 :: 32 word) < len"
    using len_ge by (simp add: word_less_nat_alt word_le_nat_alt)
  have len_gt2: "(2 :: 32 word) < len"
    using len_ge by (simp add: word_less_nat_alt word_le_nat_alt)
  have v0: "ptr_valid (heap_typing s) pending"
    using pending_valid[rule_format, of 0] len_ge
    by (simp add: word_le_nat_alt)
  have v1: "ptr_valid (heap_typing s) (pending +\<^sub>p 1)"
    using pending_valid[rule_format, of 1] len_ge
    by (simp add: word_le_nat_alt)
  have v2: "ptr_valid (heap_typing s) (pending +\<^sub>p 2)"
    using pending_valid[rule_format, of 2] len_gt2
    by (simp add: word_less_nat_alt uint_numeral)
  have p1: "heap_w8 s (pending +\<^sub>p 1) = heap_w8 s pending"
    using pending_all_eq[rule_format, of 1] len_ge
    by (simp add: word_le_nat_alt)
  have p2: "heap_w8 s (pending +\<^sub>p 2) = heap_w8 s pending"
    using pending_all_eq[rule_format, of 2] len_ge
    by (simp add: word_less_nat_alt word_le_nat_alt)
  let ?fill = "heap_w8 s pending"
  have pure_sections:
    "enc_data (flush_pending_spec src_len spec_st) =
       enc_data (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    "enc_inst (flush_pending_spec src_len spec_st) =
       enc_inst (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    "enc_addr (flush_pending_spec src_len spec_st) =
       enc_addr (emit_inst_spec src_len
         (RRun ?fill (unat len)) spec_st)"
    by (rule flush_pending_spec_heap_all_eq_run_sections[
        OF pending_eq len_ge pending_all_eq])+
  have size_unique:
    "\<And>n'. varint_size' len s = Some n' \<Longrightarrow> n' = n"
    using size by simp
  show ?thesis
    apply runs_to_vcg
    subgoal using v0 by simp
    subgoal using v1 by simp
    subgoal using v2 by simp
    subgoal
      apply (rule runs_to_weaken[
        OF flush_pending'_replicate_run_inner_loop_from_Res_int])
         apply (rule len_gt2)
        apply (rule pending_all_eq)
       apply (rule pending_valid)
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken)
       apply (rule emit_pending_run_chunk_enc_sections_state_rel[
          where src_len = src_len])
                      apply (rule rel)
                     apply (rule sec_ok)
                    apply (rule inst_byte_fits)
                   apply (rule inst_byte_ptr)
                  apply (rule inst_byte_dist)
                 apply (rule inst_byte_data_disj)
                apply (rule inst_byte_addr_disj)
               using size_unique inst_varint_fits apply blast
              using size_unique inst_varint_valid apply blast
             using size_unique inst_varint_inj apply blast
            using size_unique inst_varint_prefix_disj apply blast
           using size_unique inst_varint_no_overflow apply blast
          using size_unique inst_varint_data_disj apply blast
         using size_unique inst_varint_addr_disj apply blast
        apply (rule data_byte_fits)
       apply (rule data_byte_ptr)
      apply (rule data_byte_dist)
      using size_unique data_byte_inst_disj apply blast
      apply (rule data_byte_addr_disj)
      using pure_sections len_ge
      apply (auto simp: enc_sections_state_rel_def
                        sections_result_def word_le_nat_alt)
      done
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    subgoal using p1 p2 len_gt1 len_gt2 by (auto simp: word_le_nat_alt)
    done
qed

lemma flush_pending'_replicate_run_outer_loop_enc_sections_state_rel:
  fixes len :: "32 word"
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' len s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "(whileLoop
           (\<lambda>(add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C) st.
             i < len)
           (\<lambda>(add_start, i, sec_cur). do {
              guard (\<lambda>st.
                IS_VALID(8 word) st (pending +\<^sub>p uint i));
              b \<leftarrow> gets (\<lambda>st. heap_w8 st (pending +\<^sub>p uint i));
              j \<leftarrow> return (i + 1);
              ret \<leftarrow> liftE
                (do {
                   guard (\<lambda>st. j < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint j));
                   gets (\<lambda>st. if j < len \<and>
                     heap_w8 st (pending +\<^sub>p uint j) = b
                    then 1 else 0)
                 });
              (j, ret) \<leftarrow> liftE
                (whileLoop
                  (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
                  (\<lambda>(j, ret). do {
                     j \<leftarrow> return (j + 1);
                     x \<leftarrow> guard (\<lambda>st. j < len \<longrightarrow>
                       IS_VALID(8 word) st
                         (pending +\<^sub>p uint j));
                     ret \<leftarrow> gets (\<lambda>st. j < len \<and>
                       heap_w8 st (pending +\<^sub>p uint j) = b);
                     return (j, if ret then 1 else 0)
                  })
                  (j, ret));
              condition (\<lambda>st. (4 :: 32 word) \<le> j - i)
                (do {
                   sec_cur \<leftarrow> condition (\<lambda>st. add_start < i)
                     (do {
                        sec_cur \<leftarrow> liftE
                          (emit_add' sec_cur data data_cap inst inst_cap
                            pending add_start (i - add_start));
                        unless (sections_t_C.err_C sec_cur = ENC_OK)
                          (throw sec_cur);
                        return sec_cur
                     })
                     (return sec_cur);
                   sec_cur \<leftarrow> liftE
                     (emit_run' sec_cur data data_cap inst inst_cap
                       b (j - i));
                   unless (sections_t_C.err_C sec_cur = ENC_OK)
                     (throw sec_cur);
                   return (j, j, sec_cur)
                })
                (return (add_start, j, sec_cur))
            })
           (0, 0, sec) ::
             (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
               lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              (\<exists>sec'. r = Result (len, len, sec') \<and>
                 enc_sections_state_rel t data inst addr sec'
                   (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_unroll_exn)
   using len_ge apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply simp
  apply (subst whileLoop_unroll)
  apply simp
  apply (rule runs_to_weaken)
   apply (rule flush_pending'_replicate_run_outer_body_start_enc_sections_state_rel[
      where src_len = src_len and addr = addr and n = n, simplified])
  using rel pending_eq len_ge pending_all_eq pending_valid size sec_ok
        inst_byte_fits inst_byte_ptr inst_byte_dist inst_byte_data_disj
        inst_byte_addr_disj inst_varint_fits inst_varint_valid
        inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
        inst_varint_data_disj inst_varint_addr_disj data_byte_fits
        data_byte_ptr data_byte_dist data_byte_inst_disj data_byte_addr_disj
   apply (auto simp: word_less_nat_alt word_le_nat_alt)
  apply (rule runs_to_whileLoop_unroll_exn)
   apply simp
  apply simp
  done

lemma flush_pending'_replicate_run_outer_loop_enc_sections_state_rel_int:
  fixes len :: "32 word"
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' len s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "(whileLoop
           (\<lambda>(add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C) st.
             i < len)
           (\<lambda>(add_start, i, sec_cur). do {
              guard (\<lambda>st.
                IS_VALID(8 word) st (pending +\<^sub>p uint i));
              b \<leftarrow> gets (\<lambda>st. heap_w8 st (pending +\<^sub>p uint i));
              j \<leftarrow> return (i + 1);
              ret \<leftarrow> liftE
                (do {
                   guard (\<lambda>st. j < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint j));
                   gets (\<lambda>st. if j < len \<and>
                     heap_w8 st (pending +\<^sub>p uint j) = b
                    then 1 else 0)
                 });
              (j, ret) \<leftarrow> liftE
                (whileLoop
                  (\<lambda>(j :: 32 word, ret :: int) st. ret \<noteq> 0)
                  (\<lambda>(j, ret). do {
                     j \<leftarrow> return (j + 1);
                     x \<leftarrow> guard (\<lambda>st. j < len \<longrightarrow>
                       IS_VALID(8 word) st
                         (pending +\<^sub>p uint j));
                     ret \<leftarrow> gets (\<lambda>st. j < len \<and>
                       heap_w8 st (pending +\<^sub>p uint j) = b);
                     return (j, if ret then 1 else 0)
                  })
                  (j, ret));
              condition (\<lambda>st. (4 :: 32 word) \<le> j - i)
                (do {
                   sec_cur \<leftarrow> condition (\<lambda>st. add_start < i)
                     (do {
                        sec_cur \<leftarrow> liftE
                          (emit_add' sec_cur data data_cap inst inst_cap
                            pending add_start (i - add_start));
                        unless (sections_t_C.err_C sec_cur = ENC_OK)
                          (throw sec_cur);
                        return sec_cur
                     })
                     (return sec_cur);
                   sec_cur \<leftarrow> liftE
                     (emit_run' sec_cur data data_cap inst inst_cap
                       b (j - i));
                   unless (sections_t_C.err_C sec_cur = ENC_OK)
                     (throw sec_cur);
                   return (j, j, sec_cur)
                })
                (return (add_start, j, sec_cur))
            })
           (0, 0, sec) ::
             (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
               lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              (\<exists>sec'. r = Result (len, len, sec') \<and>
                 enc_sections_state_rel t data inst addr sec'
                   (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_unroll_exn)
   using len_ge apply (simp add: word_less_nat_alt word_le_nat_alt)
  apply simp
  apply (subst whileLoop_unroll)
  apply simp
  apply (rule runs_to_weaken)
   apply (rule flush_pending'_replicate_run_outer_body_start_enc_sections_state_rel_int[
      where src_len = src_len and addr = addr and n = n, simplified])
  using rel pending_eq len_ge pending_all_eq pending_valid size sec_ok
        inst_byte_fits inst_byte_ptr inst_byte_dist inst_byte_data_disj
        inst_byte_addr_disj inst_varint_fits inst_varint_valid
        inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
        inst_varint_data_disj inst_varint_addr_disj data_byte_fits
        data_byte_ptr data_byte_dist data_byte_inst_disj data_byte_addr_disj
   apply (auto simp: word_less_nat_alt word_le_nat_alt)
  apply (rule runs_to_whileLoop_unroll_exn)
   apply simp
  apply simp
  done

lemma flush_pending'_replicate_run_outer_loop_vcg_enc_sections_state_rel:
  fixes len :: "32 word"
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' len s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "(whileLoop
           (\<lambda>(add_start :: 32 word, i :: 32 word, sec_cur :: sections_t_C) st.
             i < len)
           (\<lambda>(add_start, i, sec_cur). do {
              guard (\<lambda>st.
                IS_VALID(8 word) st (pending +\<^sub>p uint i));
              b \<leftarrow> gets (\<lambda>st. heap_w8 st (pending +\<^sub>p uint i));
              ret \<leftarrow> liftE
                (do {
                   guard (\<lambda>st. i + 1 < len \<longrightarrow>
                     IS_VALID(8 word) st (pending +\<^sub>p uint (i + 1)));
                   gets (\<lambda>st. if i + 1 < len \<and>
                     heap_w8 st (pending +\<^sub>p uint (i + 1)) = b
                    then 1 else 0)
                 });
              (j, ret) \<leftarrow> liftE
                (whileLoop
                  (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
                  (\<lambda>(j, ret). do {
                     x \<leftarrow> guard (\<lambda>st. j + 1 < len \<longrightarrow>
                       IS_VALID(8 word) st
                         (pending +\<^sub>p uint (j + 1)));
                     ret \<leftarrow> gets (\<lambda>st. j + 1 < len \<and>
                       heap_w8 st (pending +\<^sub>p uint (j + 1)) = b);
                     return (j + 1, if ret then 1 else 0)
                  })
                  (i + 1, ret));
              condition (\<lambda>st. (4 :: 32 word) \<le> j - i)
                (do {
                   sec_cur \<leftarrow> condition (\<lambda>st. add_start < i)
                     (do {
                        sec_cur \<leftarrow> liftE
                          (emit_add' sec_cur data data_cap inst inst_cap
                            pending add_start (i - add_start));
                        unless (sections_t_C.err_C sec_cur = ENC_OK)
                          (throw sec_cur);
                        return sec_cur
                     })
                     (return sec_cur);
                   sec_cur \<leftarrow> liftE
                     (emit_run' sec_cur data data_cap inst inst_cap
                       b (j - i));
                   unless (sections_t_C.err_C sec_cur = ENC_OK)
                     (throw sec_cur);
                   return (j, j, sec_cur)
                })
                (return (add_start, j, sec_cur))
            })
           (0, 0, sec) ::
             (sections_t_C, 32 word \<times> 32 word \<times> sections_t_C,
               lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t.
              (\<exists>sec'. r = Result (len, len, sec') \<and>
                 enc_sections_state_rel t data inst addr sec'
                   (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule flush_pending'_replicate_run_outer_loop_enc_sections_state_rel[
    where n = n and src_len = src_len, simplified])
  using rel pending_eq len_ge pending_all_eq pending_valid size sec_ok
        inst_byte_fits inst_byte_ptr inst_byte_dist inst_byte_data_disj
        inst_byte_addr_disj inst_varint_fits inst_varint_valid
        inst_varint_inj inst_varint_prefix_disj inst_varint_no_overflow
        inst_varint_data_disj inst_varint_addr_disj data_byte_fits
        data_byte_ptr data_byte_dist data_byte_inst_disj data_byte_addr_disj
  by auto

lemma flush_pending'_replicate_run_enc_sections_state_rel:
  fixes len :: "32 word"
  assumes rel:
        "enc_sections_state_rel s data inst addr sec spec_st"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 len"
      and len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and size: "varint_size' len s = Some n"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_varint_fits:
        "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      and inst_varint_valid: "\<forall>j < unat n.
        ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      and inst_varint_inj: "\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      and inst_varint_prefix_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < n \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      and inst_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and inst_varint_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < n \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      and data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
      and data_byte_ptr:
        "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      and data_byte_dist:
        "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
      and data_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1 + n).
           inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      and data_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  shows "flush_pending' sec data data_cap inst inst_cap pending len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec'
                  (flush_pending_spec src_len spec_st)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  unfolding flush_pending'_def
  apply runs_to_vcg
  apply (rule runs_to_weaken[
    where Q = "\<lambda>r t.
      (\<exists>sec'. r = Result (len, len, sec') \<and>
        enc_sections_state_rel t data inst addr sec'
          (flush_pending_spec src_len spec_st)) \<and>
      heap_typing t = heap_typing s"])
   apply (rule flush_pending'_replicate_run_outer_loop_enc_sections_state_rel_int[
      where n = n and src_len = src_len])
                         apply (rule rel)
                        apply (rule pending_eq)
                       apply (rule len_ge)
                      apply (rule pending_all_eq)
                     apply (rule pending_valid)
                    apply (rule size)
                   apply (rule sec_ok)
                  apply (rule inst_byte_fits)
                 apply (rule inst_byte_ptr)
                apply (rule inst_byte_dist)
               apply (rule inst_byte_data_disj)
              apply (rule inst_byte_addr_disj)
             apply (rule inst_varint_fits)
            apply (rule inst_varint_valid)
           apply (rule inst_varint_inj)
          apply (rule inst_varint_prefix_disj)
         apply (rule inst_varint_no_overflow)
        apply (rule inst_varint_data_disj)
       apply (rule inst_varint_addr_disj)
      apply (rule data_byte_fits)
     apply (rule data_byte_ptr)
    apply (rule data_byte_dist)
   apply (rule data_byte_inst_disj)
  apply (rule data_byte_addr_disj)
  subgoal premises loop_post for r t
  proof -
    obtain sec' where r_def: "r = Result (len, len, sec')"
      and rel': "enc_sections_state_rel t data inst addr sec'
        (flush_pending_spec src_len spec_st)"
      and typing: "heap_typing t = heap_typing s"
      using loop_post by auto
    show ?thesis
      apply (simp add: r_def typing)
      apply runs_to_vcg
      using rel' typing by auto
  qed
  done

lemma flush_pending'_replicate_run_inner_loop:
  fixes len :: "32 word"
  assumes len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                  heap_w8 s pending);
              return (j + 1, if ret then 1 else 0)
           }) (1, 1) :: (32 word \<times> 32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (len, 0) \<and> t = s \<rbrace>"
  apply (rule flush_pending'_replicate_run_inner_loop_from[
    OF _ pending_all_eq pending_valid])
  using len_ge by (simp add: word_less_nat_alt word_le_nat_alt)

lemma flush_pending'_replicate_run_inner_loop_Res:
  fixes len :: "32 word"
  assumes len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
           (\<lambda>(j, ret). do {
              x \<leftarrow> guard
                (\<lambda>st. j + 1 < len \<longrightarrow>
                  IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
              ret \<leftarrow> gets
                (\<lambda>st. j + 1 < len \<and>
                  heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                  heap_w8 s pending);
              return (j + 1, if ret then 1 else 0)
           }) (1, 1) :: (32 word \<times> 32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>Res r t. r = (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_weaken[
    where Q = "\<lambda>r t. r = Result (len, 0) \<and> t = s"])
   apply (rule flush_pending'_replicate_run_inner_loop)
     apply (rule len_ge)
    apply (rule pending_all_eq)
   apply (rule pending_valid)
  by auto

lemma flush_pending'_replicate_run_inner_loop_liftE:
  fixes len :: "32 word"
  assumes len_ge: "(4 :: 32 word) \<le> len"
      and pending_all_eq: "\<forall>j < unat len.
        heap_w8 s (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j)) =
        heap_w8 s pending"
      and pending_valid: "\<forall>j < unat len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
  shows "(liftE
           ((whileLoop (\<lambda>(j :: 32 word, ret :: 32 word) st. ret \<noteq> 0)
             (\<lambda>(j, ret). do {
                x \<leftarrow> guard
                  (\<lambda>st. j + 1 < len \<longrightarrow>
                    IS_VALID(8 word) st (pending +\<^sub>p uint (j + 1)));
                ret \<leftarrow> gets
                  (\<lambda>st. j + 1 < len \<and>
                    heap_w8 st (pending +\<^sub>p uint (j + 1)) =
                    heap_w8 s pending);
                return (j + 1, if ret then 1 else 0)
             }) (1, 1)) ::
              (32 word \<times> 32 word, lifted_globals) res_monad)
          :: ('e, 32 word \<times> 32 word, lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (len, 0) \<and> t = s \<rbrace>"
  apply (rule runs_to_liftE)
  apply (rule runs_to_weaken[
    OF flush_pending'_replicate_run_inner_loop_Res])
     apply (rule len_ge)
    apply (rule pending_all_eq)
   apply (rule pending_valid)
  by auto

lemma try_emit_add_copy'_pend_len_zero_noop:
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending 0 copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f. r = Result f \<and>
                   fused_t_C.s_C f = sec \<and>
                   fused_t_C.fused_C f = 0) \<and>
              t = s \<rbrace>"
  unfolding try_emit_add_copy'_def
  apply runs_to_vcg
  done

lemma try_emit_add_copy'_pend_len_zero_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending 0 copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.s_C f = sec \<and>
                fused_t_C.fused_C f = 0 \<and>
                enc_sections_inv t data inst addr_buf (fused_t_C.s_C f)
                  src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF try_emit_add_copy'_pend_len_zero_noop])
  using inv abs cache_wf by auto

lemma try_emit_add_copy'_pend_len_zero_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and pending_empty: "enc_pending spec_st = []"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending 0 copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.s_C f = sec \<and>
                fused_t_C.fused_C f = 0 \<and>
                try_emit_add_copy_spec src_len (unat copy_addr)
                  (unat copy_len) spec_st = None \<and>
                enc_sections_state_rel t data inst addr_buf
                  (fused_t_C.s_C f) spec_st) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF try_emit_add_copy'_pend_len_zero_noop])
  using rel try_emit_add_copy_spec_pending_empty_none[OF pending_empty]
  by auto

lemma try_emit_add_copy'_early_noop:
  assumes early:
    "pend_len < (1 :: 32 word) \<or>
     (4 :: 32 word) < pend_len \<or>
     copy_len < (4 :: 32 word)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f. r = Result f \<and>
                   fused_t_C.s_C f = sec \<and>
                   fused_t_C.fused_C f = 0) \<and>
              t = s \<rbrace>"
  unfolding try_emit_add_copy'_def
  apply runs_to_vcg
  using early by auto

lemma try_emit_add_copy'_early_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and early:
        "pend_len < (1 :: 32 word) \<or>
         (4 :: 32 word) < pend_len \<or>
         copy_len < (4 :: 32 word)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.s_C f = sec \<and>
                fused_t_C.fused_C f = 0 \<and>
                enc_sections_inv t data inst addr_buf (fused_t_C.s_C f)
                  src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF try_emit_add_copy'_early_noop[OF early]])
  using inv abs cache_wf by auto

lemma try_emit_add_copy'_early_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and pending_len: "length (enc_pending spec_st) = unat pend_len"
      and early:
        "pend_len < (1 :: 32 word) \<or>
         (4 :: 32 word) < pend_len \<or>
         copy_len < (4 :: 32 word)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.s_C f = sec \<and>
                fused_t_C.fused_C f = 0 \<and>
                try_emit_add_copy_spec src_len (unat copy_addr)
                  (unat copy_len) spec_st = None \<and>
                enc_sections_state_rel t data inst addr_buf
                  (fused_t_C.s_C f) spec_st) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF try_emit_add_copy'_early_noop[OF early]])
  using rel try_emit_add_copy_spec_early_none[OF pending_len early]
  by auto

lemma try_emit_add_copy'_mode_gt5_copy_ne4_noop:
  assumes bm: "best_mode' copy_addr here s = Some m"
      and mode_gt: "(5 :: 32 word) < mode_t_C.mode_C m"
      and copy_ne: "copy_len \<noteq> (4 :: 32 word)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f. r = Result f \<and>
                   fused_t_C.s_C f = sec \<and>
                   fused_t_C.fused_C f = 0) \<and>
              t = s \<rbrace>"
  unfolding try_emit_add_copy'_def
  apply runs_to_vcg
  apply (rule exI[where x = m])
  using bm mode_gt copy_ne
  apply (auto simp: word_less_nat_alt word_le_nat_alt)
   apply runs_to_vcg
  apply runs_to_vcg
  done

lemma try_emit_add_copy'_mode_gt5_copy_ne4_enc_sections_cache_inv:
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and mode_gt: "(5 :: 32 word) < mode_t_C.mode_C m"
      and copy_ne: "copy_len \<noteq> (4 :: 32 word)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.s_C f = sec \<and>
                fused_t_C.fused_C f = 0 \<and>
                enc_sections_inv t data inst addr_buf (fused_t_C.s_C f)
                  src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF try_emit_add_copy'_mode_gt5_copy_ne4_noop
      [OF bm mode_gt copy_ne]])
  using inv abs cache_wf by auto

lemma try_emit_add_copy'_mode_gt5_copy_ne4_enc_sections_state_rel:
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and bm: "best_mode' copy_addr here s = Some m"
      and mode_gt: "(5 :: 32 word) < mode_t_C.mode_C m"
      and copy_ne: "copy_len \<noteq> (4 :: 32 word)"
      and addr_choice:
        "encode_address (enc_cache spec_st) (unat copy_addr)
           (src_len + enc_tp spec_st) =
         (unat (mode_t_C.mode_C m), addr_bytes, cache')"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.s_C f = sec \<and>
                fused_t_C.fused_C f = 0 \<and>
                try_emit_add_copy_spec src_len (unat copy_addr)
                  (unat copy_len) spec_st = None \<and>
                enc_sections_state_rel t data inst addr_buf
                  (fused_t_C.s_C f) spec_st) \<and>
              heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF try_emit_add_copy'_mode_gt5_copy_ne4_noop
      [OF bm mode_gt copy_ne]])
  using rel try_emit_add_copy_spec_mode_gt5_copy_ne4_none
      [OF addr_choice mode_gt copy_ne]
  by auto

lemma try_emit_add_copy'_mode_gt5_success_emitted_sections:
  fixes op pend_len :: "32 word"
    and m
  defines "op \<equiv>
    (235 + (mode_t_C.mode_C m - 6) * 4 + (pend_len - 1) :: 32 word)"
  assumes emitted:
        "emitted_sections s data inst addr_buf sec data_bytes inst_bytes addr_bytes"
      and bm: "best_mode' copy_addr here s = Some m"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_eq: "copy_len = (4 :: 32 word)"
      and mode_gt: "(5 :: 32 word) < mode_t_C.mode_C m"
      and mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat pend_len.
           pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < pend_len"
      and data_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (of_nat j :: 32 word))"
      and data_pending_disj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (of_nat j :: 32 word)"
      and data_inj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat pend_len < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < pend_len \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec + pend_len).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.fused_C f = copy_len \<and>
                sections_result (fused_t_C.s_C f)
                  (sections_t_C.data_pos_C sec + pend_len)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                emitted_sections t data inst addr_buf (fused_t_C.s_C f)
                  (data_bytes @ heap_bytes_word s pending 0 pend_len)
                  (inst_bytes @ [ucast op])
                  (addr_bytes @ [ucast (mode_t_C.arg_C m)])) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op_nz:
    "(0xD2 + (mode_t_C.mode_C m * 4 + pend_len) :: 32 word) \<noteq> 0"
    using pend_ge pend_le mode_gt mode_le
    by (auto simp: word_less_nat_alt word_le_nat_alt
                   word_neq_0_conv unat_word_ariths)
  have inst_write_frame:
    "write_byte' inst inst_cap (sections_t_C.inst_pos_C sec)
       (ucast (0xD2 + (mode_t_C.mode_C m * 4 + pend_len) :: 32 word)) \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (sections_t_C.inst_pos_C sec + 1) ENC_OK) \<and>
               heap_bytes t inst (unat (sections_t_C.inst_pos_C sec + 1)) =
               heap_bytes s inst (unat (sections_t_C.inst_pos_C sec)) @
                 [ucast (0xD2 + (mode_t_C.mode_C m * 4 + pend_len) :: 32 word)] \<and>
               heap_bytes t data (unat (sections_t_C.data_pos_C sec)) =
               heap_bytes s data (unat (sections_t_C.data_pos_C sec)) \<and>
               heap_bytes t addr_buf (unat (sections_t_C.addr_pos_C sec)) =
               heap_bytes s addr_buf (unat (sections_t_C.addr_pos_C sec)) \<and>
               heap_bytes_word t pending 0 pend_len =
               heap_bytes_word s pending 0 pend_len \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule write_byte'_heap_bytes_append_next_typing_preserves2_word)
         apply (rule inst_byte_fits)
        apply (rule inst_byte_ptr)
       apply (rule inst_byte_dist)
      apply (rule inst_byte_data_disj)
     apply (rule inst_byte_addr_disj)
    using inst_byte_pending_disj apply simp
    done
  have inst_write_near:
    "write_byte' inst inst_cap (sections_t_C.inst_pos_C sec)
       (ucast (0xD2 + (mode_t_C.mode_C m * 4 + pend_len) :: 32 word)) \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (sections_t_C.inst_pos_C sec + 1) ENC_OK) \<and>
               near_ptr_'' t = near_ptr_'' s \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule runs_to_weaken[OF write_byte'_spec])
     apply (rule inst_byte_ptr)
    using inst_byte_fits by auto
  have inst_write:
    "write_byte' inst inst_cap (sections_t_C.inst_pos_C sec)
       (ucast (0xD2 + (mode_t_C.mode_C m * 4 + pend_len) :: 32 word)) \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (sections_t_C.inst_pos_C sec + 1) ENC_OK) \<and>
               heap_bytes t inst (unat (sections_t_C.inst_pos_C sec + 1)) =
               heap_bytes s inst (unat (sections_t_C.inst_pos_C sec)) @
                 [ucast (0xD2 + (mode_t_C.mode_C m * 4 + pend_len) :: 32 word)] \<and>
               heap_bytes t data (unat (sections_t_C.data_pos_C sec)) =
               heap_bytes s data (unat (sections_t_C.data_pos_C sec)) \<and>
               heap_bytes t addr_buf (unat (sections_t_C.addr_pos_C sec)) =
               heap_bytes s addr_buf (unat (sections_t_C.addr_pos_C sec)) \<and>
               heap_bytes_word t pending 0 pend_len =
               heap_bytes_word s pending 0 pend_len \<and>
               near_ptr_'' t = near_ptr_'' s \<and>
               heap_typing t = heap_typing s \<rbrace>"
    using inst_write_frame inst_write_near
    by (simp add: runs_to_conj)
  have data_write:
    "\<And>st. heap_typing st = heap_typing s \<Longrightarrow>
      write_bytes' data data_cap (sections_t_C.data_pos_C sec)
        pending 0 pend_len \<bullet> st
       \<lbrace> \<lambda>r t. r = Result
                 (wr_t_C (sections_t_C.data_pos_C sec + pend_len) ENC_OK) \<and>
               heap_bytes t data
                 (unat (sections_t_C.data_pos_C sec + pend_len)) =
               heap_bytes st data (unat (sections_t_C.data_pos_C sec)) @
                 heap_bytes_word st pending 0 pend_len \<and>
               heap_bytes t inst (unat (sections_t_C.inst_pos_C sec + 1)) =
               heap_bytes st inst (unat (sections_t_C.inst_pos_C sec + 1)) \<and>
               heap_bytes t addr_buf (unat (sections_t_C.addr_pos_C sec)) =
               heap_bytes st addr_buf (unat (sections_t_C.addr_pos_C sec)) \<and>
               near_ptr_'' t = near_ptr_'' st \<and>
               heap_typing t = heap_typing st \<rbrace>"
    apply (rule write_bytes'_success_heap_bytes_append_wordpos_preserves2_near_ptr)
            apply (rule data_fits)
           apply (clarsimp)
           using data_valid apply blast
          apply (clarsimp)
          using pending_valid apply blast
         apply (simp add: data_pending_disj)
        apply (rule data_inj)
       apply (rule data_prefix_disj)
      apply (rule data_no_overflow)
     apply (rule data_inst_disj)
    apply (rule data_addr_disj)
    done
  note gets_the_best_mode'_result[runs_to_vcg]
  note add_copy_opcode'_mode_gt5[runs_to_vcg]
  show ?thesis
    unfolding try_emit_add_copy'_def op_def
    using bm pend_ge pend_le copy_eq mode_gt mode_le
    apply runs_to_vcg
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt word_le_nat_alt
                              word_neq_0_conv unat_word_ariths)
    using op_nz apply simp
        apply (rule runs_to_weaken[OF inst_write])
       apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken)
        apply (rule data_write)
        apply simp
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF emit_address'_success_byte_heap_bytes_append_preserves2_near_ptr])
           using mode_gt apply (simp add: word_less_nat_alt)
          apply (rule addr_byte_fits)
         apply (simp add: addr_byte_ptr)
        apply (rule addr_byte_dist)
       apply (rule addr_byte_data_disj)
      apply (rule addr_byte_inst_disj)
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF cache_update'_preserves_heap_bytes3
        [of _ _ data "unat (sections_t_C.data_pos_C sec + pend_len)"
           inst "unat (sections_t_C.inst_pos_C sec + 1)"
           addr_buf "unat (sections_t_C.addr_pos_C sec + 1)"]])
      using near_ptr_lt apply simp
    using emitted sec_ok
    apply (clarsimp simp: sections_result_def emitted_sections_def)
    done
qed

lemma try_emit_add_copy'_mode_gt5_success_enc_sections_inv:
  fixes op pend_len :: "32 word"
    and m
  defines "op \<equiv>
    (235 + (mode_t_C.mode_C m - 6) * 4 + (pend_len - 1) :: 32 word)"
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_eq: "copy_len = (4 :: 32 word)"
      and mode_gt: "(5 :: 32 word) < mode_t_C.mode_C m"
      and mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
      and here_eq:
        "unat here = length src_seg + length target + unat pend_len"
      and addr_ok:
        "unat copy_addr < length src_seg + length target + unat pend_len"
      and target_room:
        "length target + unat pend_len + unat copy_len \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat pend_len.
           pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < pend_len"
      and data_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (of_nat j :: 32 word))"
      and data_pending_disj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (of_nat j :: 32 word)"
      and data_inj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat pend_len < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < pend_len \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec + pend_len).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.fused_C f = copy_len \<and>
                sections_result (fused_t_C.s_C f)
                  (sections_t_C.data_pos_C sec + pend_len)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + 1)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf (fused_t_C.s_C f)
                  src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending 0 pend_len)
                  (inst_bytes @ [ucast op])
                  (addr_bytes @ [ucast (mode_t_C.arg_C m)])
                  (copy_loop src_seg
                    (target @ heap_bytes_word s pending 0 pend_len)
                    (unat copy_addr) (unat copy_len))
                  (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?add = "heap_bytes_word s pending 0 pend_len"
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf:
    "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
    using mode_gt by (simp add: word_less_nat_alt)
  have fop:
    "find_add_copy_opcode (length ?add) (unat copy_len)
       (unat (mode_t_C.mode_C m)) = Some (unat op)"
    unfolding op_def
    using add_copy_opcode_word_mode_gt5_find[
      OF pend_ge pend_le mode_gt mode_le copy_eq]
    by simp
  have op_byte: "(word_of_nat (unat op) :: byte) = ucast op"
    by (rule byte_of_unat_ucast32)
  have here_eq_add:
    "unat here = length src_seg + length target + length ?add"
    using here_eq by simp
  have addr_ok_add:
    "unat copy_addr < length src_seg + length target + length ?add"
    using addr_ok by simp
  have target_room_add:
    "length target + length ?add + unat copy_len \<le> tgt_len"
    using target_room by simp
  have decodes_post:
    "section_decodes src_seg tgt_len
       (data_bytes @ ?add)
       (inst_bytes @ [ucast op])
       (addr_bytes @ [ucast (mode_t_C.arg_C m)])
       (copy_loop src_seg (target @ ?add) (unat copy_addr) (unat copy_len))
       (cache_update c_out (unat copy_addr))"
    using section_decodes_fused_add_copy_append_byte_addr
      [OF enc_sections_invD(2)[OF inv] fop mode_wf mode_ge here_eq_add
          addr_ok_add target_room_add] op_byte
    by simp
  show ?thesis
    apply (rule runs_to_weaken[
      OF try_emit_add_copy'_mode_gt5_success_emitted_sections
        [OF enc_sections_invD(1)[OF inv] bm pend_ge pend_le copy_eq
            mode_gt mode_le sec_ok near_ptr_lt inst_byte_fits inst_byte_ptr
            inst_byte_dist inst_byte_data_disj inst_byte_addr_disj
            inst_byte_pending_disj data_fits data_valid pending_valid
            data_pending_disj data_inj data_prefix_disj data_no_overflow
            data_inst_disj data_addr_disj addr_byte_fits addr_byte_ptr
            addr_byte_dist addr_byte_data_disj addr_byte_inst_disj,
          folded op_def]])
    using decodes_post by (auto simp: enc_sections_inv_def)
qed

lemma try_emit_add_copy'_mode_gt5_success_enc_sections_state_rel:
  fixes op pend_len :: "32 word"
    and m
  defines "op \<equiv>
    (235 + (mode_t_C.mode_C m - 6) * 4 + (pend_len - 1) :: 32 word)"
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 pend_len"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_eq: "copy_len = (4 :: 32 word)"
      and mode_gt: "(5 :: 32 word) < mode_t_C.mode_C m"
      and mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
      and addr_choice:
        "encode_address (enc_cache spec_st) (unat copy_addr)
           (src_len + enc_tp spec_st) =
         (unat (mode_t_C.mode_C m), [ucast (mode_t_C.arg_C m)],
          cache_update (enc_cache spec_st) (unat copy_addr))"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat pend_len.
           pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < pend_len"
      and data_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (of_nat j :: 32 word))"
      and data_pending_disj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (of_nat j :: 32 word)"
      and data_inj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat pend_len < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < pend_len \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec + pend_len).
           data +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_byte_inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1).
           inst +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f spec_st'.
                r = Result f \<and>
                fused_t_C.fused_C f = copy_len \<and>
                try_emit_add_copy_spec src_len (unat copy_addr)
                  (unat copy_len) spec_st = Some spec_st' \<and>
                enc_sections_state_rel t data inst addr_buf
                  (fused_t_C.s_C f) spec_st') \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have pending_len: "length (enc_pending spec_st) = unat pend_len"
    using pending_eq by simp
  have spec_success:
    "try_emit_add_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st =
      Some (spec_st
        \<lparr> enc_tp := enc_tp spec_st + unat copy_len
         , enc_flushed := enc_flushed spec_st + unat pend_len + unat copy_len
         , enc_pending := []
         , enc_data := enc_data spec_st @ enc_pending spec_st
         , enc_inst := enc_inst spec_st @ [ucast op]
         , enc_addr := enc_addr spec_st @ [ucast (mode_t_C.arg_C m)]
         , enc_cache := cache_update (enc_cache spec_st) (unat copy_addr)
         , enc_trace := enc_trace spec_st
             @ [RAdd (enc_pending spec_st),
                RCopy (unat copy_addr) (unat copy_len)]
         \<rparr>)"
    unfolding op_def
    by (rule try_emit_add_copy_spec_mode_gt5_success
      [OF pending_len pend_ge pend_le copy_eq mode_gt mode_le addr_choice])
  show ?thesis
    apply (rule runs_to_weaken[
      OF try_emit_add_copy'_mode_gt5_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] bm pend_ge pend_le
            copy_eq mode_gt mode_le sec_ok near_ptr_lt inst_byte_fits
            inst_byte_ptr inst_byte_dist inst_byte_data_disj
            inst_byte_addr_disj inst_byte_pending_disj data_fits data_valid
            pending_valid data_pending_disj data_inj data_prefix_disj
            data_no_overflow data_inst_disj data_addr_disj addr_byte_fits
            addr_byte_ptr addr_byte_dist addr_byte_data_disj
            addr_byte_inst_disj, folded op_def]])
  using spec_success pending_eq
  by (auto simp: enc_sections_state_rel_def)
qed

lemma try_emit_add_copy'_mode_le5_success_emitted_sections:
  fixes csz op pend_len copy_len :: "32 word"
    and m
  defines "csz \<equiv>
    (if (6 :: 32 word) < copy_len then (6 :: 32 word) else copy_len)"
    and "op \<equiv>
      (163 + mode_t_C.mode_C m * 12 + (pend_len - 1) * 3 + (csz - 4) ::
        32 word)"
  assumes emitted:
        "emitted_sections s data inst addr_buf sec data_bytes inst_bytes addr_bytes"
      and bm: "best_mode' copy_addr here s = Some m"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_len"
      and mode_le: "mode_t_C.mode_C m \<le> (5 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat pend_len.
           pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < pend_len"
      and data_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (of_nat j :: 32 word))"
      and data_pending_disj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (of_nat j :: 32 word)"
      and data_inj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat pend_len < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < pend_len \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec + pend_len). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj:
        "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.fused_C f = csz \<and>
                sections_result (fused_t_C.s_C f)
                  (sections_t_C.data_pos_C sec + pend_len)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                emitted_sections t data inst addr_buf (fused_t_C.s_C f)
                  (data_bytes @ heap_bytes_word s pending 0 pend_len)
                  (inst_bytes @ [ucast op])
                  (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have csz_ge: "(4 :: 32 word) \<le> csz"
    using copy_ge unfolding csz_def
    by (auto simp: word_less_nat_alt word_le_nat_alt)
  have csz_le: "csz \<le> (6 :: 32 word)"
    using copy_ge unfolding csz_def
    by (auto simp: word_less_nat_alt word_le_nat_alt)
  have mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
    using mode_le by (simp add: word_less_nat_alt word_le_nat_alt)
  have op_nz:
    "op \<noteq> (0 :: 32 word)"
    using pend_ge pend_le mode_le csz_ge csz_le
    unfolding op_def
    by (auto simp: word_less_nat_alt word_le_nat_alt
                   word_neq_0_conv unat_word_ariths)
  have op_nz_gt6_expr:
    "(0xA2 + (mode_t_C.mode_C m * 0xC + pend_len * 3) :: 32 word) \<noteq> 0"
  proof -
    have mode_nat: "unat (mode_t_C.mode_C m) \<le> 5"
      using mode_le by (simp add: word_le_nat_alt)
    have pend_nat: "1 \<le> unat pend_len" "unat pend_len \<le> 4"
      using pend_ge pend_le by (simp_all add: word_le_nat_alt)
    have expr_unat:
      "unat (0xA2 + (mode_t_C.mode_C m * 0xC + pend_len * 3) :: 32 word) =
       162 + (unat (mode_t_C.mode_C m) * 12 + unat pend_len * 3)"
      using mode_nat pend_nat
      by (simp add: unat_word_ariths)
    show ?thesis
      using expr_unat pend_nat by auto
  qed
  have op_nz_le6_expr:
    "\<not> (6 :: 32 word) < copy_len \<Longrightarrow>
      (0x9C + (mode_t_C.mode_C m * 0xC + (pend_len * 3 + copy_len)) ::
        32 word) \<noteq> 0"
  proof -
    assume copy_le6: "\<not> (6 :: 32 word) < copy_len"
    have mode_nat: "unat (mode_t_C.mode_C m) \<le> 5"
      using mode_le by (simp add: word_le_nat_alt)
    have pend_nat: "1 \<le> unat pend_len" "unat pend_len \<le> 4"
      using pend_ge pend_le by (simp_all add: word_le_nat_alt)
    have copy_nat: "4 \<le> unat copy_len" "unat copy_len \<le> 6"
      using copy_ge copy_le6
      by (simp_all add: word_le_nat_alt word_less_nat_alt)
    have expr_unat:
      "unat (0x9C + (mode_t_C.mode_C m * 0xC + (pend_len * 3 + copy_len)) ::
          32 word) =
       156 + (unat (mode_t_C.mode_C m) * 12 +
          (unat pend_len * 3 + unat copy_len))"
      using mode_nat pend_nat copy_nat
      by (simp add: unat_word_ariths)
    show ?thesis
      using expr_unat pend_nat copy_nat by auto
  qed
  have inst_write_frame:
    "\<And>opb :: 32 word.
     write_byte' inst inst_cap (sections_t_C.inst_pos_C sec) (ucast opb) \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (sections_t_C.inst_pos_C sec + 1) ENC_OK) \<and>
               heap_bytes t inst (unat (sections_t_C.inst_pos_C sec + 1)) =
               heap_bytes s inst (unat (sections_t_C.inst_pos_C sec)) @
                 [ucast opb] \<and>
               heap_bytes t data (unat (sections_t_C.data_pos_C sec)) =
               heap_bytes s data (unat (sections_t_C.data_pos_C sec)) \<and>
               heap_bytes t addr_buf (unat (sections_t_C.addr_pos_C sec)) =
               heap_bytes s addr_buf (unat (sections_t_C.addr_pos_C sec)) \<and>
               heap_bytes_word t pending 0 pend_len =
               heap_bytes_word s pending 0 pend_len \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule write_byte'_heap_bytes_append_next_typing_preserves2_word)
         apply (rule inst_byte_fits)
        apply (rule inst_byte_ptr)
       apply (rule inst_byte_dist)
      apply (rule inst_byte_data_disj)
     apply (rule inst_byte_addr_disj)
    using inst_byte_pending_disj apply simp
    done
  have inst_write_near:
    "\<And>opb :: 32 word.
     write_byte' inst inst_cap (sections_t_C.inst_pos_C sec) (ucast opb) \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (sections_t_C.inst_pos_C sec + 1) ENC_OK) \<and>
               near_ptr_'' t = near_ptr_'' s \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule runs_to_weaken[OF write_byte'_spec])
     apply (rule inst_byte_ptr)
    using inst_byte_fits by auto
  have inst_write:
    "\<And>opb :: 32 word.
     write_byte' inst inst_cap (sections_t_C.inst_pos_C sec) (ucast opb) \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (sections_t_C.inst_pos_C sec + 1) ENC_OK) \<and>
               heap_bytes t inst (unat (sections_t_C.inst_pos_C sec + 1)) =
               heap_bytes s inst (unat (sections_t_C.inst_pos_C sec)) @
                 [ucast opb] \<and>
               heap_bytes t data (unat (sections_t_C.data_pos_C sec)) =
               heap_bytes s data (unat (sections_t_C.data_pos_C sec)) \<and>
               heap_bytes t addr_buf (unat (sections_t_C.addr_pos_C sec)) =
               heap_bytes s addr_buf (unat (sections_t_C.addr_pos_C sec)) \<and>
               heap_bytes_word t pending 0 pend_len =
               heap_bytes_word s pending 0 pend_len \<and>
               near_ptr_'' t = near_ptr_'' s \<and>
               heap_typing t = heap_typing s \<rbrace>"
    using inst_write_frame inst_write_near
    by (simp add: runs_to_conj)
  have data_write:
    "\<And>st. heap_typing st = heap_typing s \<Longrightarrow>
      write_bytes' data data_cap (sections_t_C.data_pos_C sec)
        pending 0 pend_len \<bullet> st
       \<lbrace> \<lambda>r t. r = Result
                 (wr_t_C (sections_t_C.data_pos_C sec + pend_len) ENC_OK) \<and>
               heap_bytes t data
                 (unat (sections_t_C.data_pos_C sec + pend_len)) =
               heap_bytes st data (unat (sections_t_C.data_pos_C sec)) @
                 heap_bytes_word st pending 0 pend_len \<and>
               heap_bytes t inst (unat (sections_t_C.inst_pos_C sec + 1)) =
               heap_bytes st inst (unat (sections_t_C.inst_pos_C sec + 1)) \<and>
               heap_bytes t addr_buf (unat (sections_t_C.addr_pos_C sec)) =
               heap_bytes st addr_buf (unat (sections_t_C.addr_pos_C sec)) \<and>
               near_ptr_'' t = near_ptr_'' st \<and>
               heap_typing t = heap_typing st \<rbrace>"
    apply (rule write_bytes'_success_heap_bytes_append_wordpos_preserves2_near_ptr)
            apply (rule data_fits)
           apply (clarsimp)
           using data_valid apply blast
          apply (clarsimp)
          using pending_valid apply blast
         apply (simp add: data_pending_disj)
        apply (rule data_inj)
       apply (rule data_prefix_disj)
      apply (rule data_no_overflow)
     apply (rule data_inst_disj)
    apply (rule data_addr_disj)
    done
  have addr_write:
    "\<And>st. heap_typing st = heap_typing s \<Longrightarrow>
      emit_address' addr_buf addr_cap (sections_t_C.addr_pos_C sec) m \<bullet> st
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (sections_t_C.addr_pos_C sec + an) ENC_OK) \<and>
               heap_bytes t addr_buf
                 (unat (sections_t_C.addr_pos_C sec + an)) =
               heap_bytes st addr_buf (unat (sections_t_C.addr_pos_C sec)) @
                 varint_bytes32 (mode_t_C.arg_C m) an \<and>
               heap_bytes t data
                 (unat (sections_t_C.data_pos_C sec + pend_len)) =
               heap_bytes st data
                 (unat (sections_t_C.data_pos_C sec + pend_len)) \<and>
               heap_bytes t inst (unat (sections_t_C.inst_pos_C sec + 1)) =
               heap_bytes st inst (unat (sections_t_C.inst_pos_C sec + 1)) \<and>
               near_ptr_'' t = near_ptr_'' st \<and>
               heap_typing t = heap_typing st \<rbrace>"
    apply (rule emit_address'_success_varint_heap_bytes_append_preserves2_near_ptr
      [where n = an])
            apply (rule mode_lt)
           subgoal for st
             using addr_size varint_size'_state_independent
               [of "mode_t_C.arg_C m" st s] by simp
          apply (rule addr_varint_fits)
         apply (clarsimp)
         using addr_varint_valid apply blast
        apply (rule addr_varint_inj)
       apply (rule addr_varint_prefix_disj)
      apply (rule addr_varint_no_overflow)
     apply (rule addr_varint_data_disj)
    apply (rule addr_varint_inst_disj)
    done
  note gets_the_best_mode'_result[runs_to_vcg]
  note add_copy_opcode'_mode_le5[runs_to_vcg]
  show ?thesis
    unfolding try_emit_add_copy'_def csz_def op_def
    using bm pend_ge pend_le copy_ge mode_le csz_ge csz_le op_nz
    apply runs_to_vcg
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt word_le_nat_alt
                         word_neq_0_conv unat_word_ariths)
    using op_nz_gt6_expr apply simp
       apply (rule runs_to_weaken[OF inst_write])
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken)
       apply (rule data_write)
       apply simp
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule addr_write)
      apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF cache_update'_preserves_heap_bytes3
       [of _ _ data "unat (sections_t_C.data_pos_C sec + pend_len)"
          inst "unat (sections_t_C.inst_pos_C sec + 1)"
          addr_buf "unat (sections_t_C.addr_pos_C sec + an)"]])
     using near_ptr_lt apply simp
    using emitted sec_ok
    apply (clarsimp simp: sections_result_def emitted_sections_def
                          csz_def op_def)
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt word_le_nat_alt
                         word_neq_0_conv unat_word_ariths)
    using op_nz_le6_expr apply (auto simp: word_less_nat_alt)
       apply (rule runs_to_weaken[OF inst_write])
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken)
       apply (rule data_write)
       apply simp
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken)
      apply (rule addr_write)
      apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF cache_update'_preserves_heap_bytes3
       [of _ _ data "unat (sections_t_C.data_pos_C sec + pend_len)"
          inst "unat (sections_t_C.inst_pos_C sec + 1)"
          addr_buf "unat (sections_t_C.addr_pos_C sec + an)"]])
     using near_ptr_lt apply simp
    using emitted sec_ok
    apply (clarsimp simp: sections_result_def emitted_sections_def
                          csz_def op_def)
    done
qed

lemma try_emit_add_copy'_mode_le5_success_enc_sections_inv:
  fixes csz op pend_len copy_len :: "32 word"
    and m
  defines "csz \<equiv>
    (if (6 :: 32 word) < copy_len then (6 :: 32 word) else copy_len)"
    and "op \<equiv>
      (163 + mode_t_C.mode_C m * 12 + (pend_len - 1) * 3 + (csz - 4) ::
        32 word)"
  assumes inv:
        "enc_sections_inv s data inst addr_buf sec src_seg tgt_len
          data_bytes inst_bytes addr_bytes target c_out"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_len"
      and mode_le: "mode_t_C.mode_C m \<le> (5 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and here_eq:
        "unat here = length src_seg + length target + unat pend_len"
      and addr_ok:
        "unat copy_addr < length src_seg + length target + unat pend_len"
      and target_room:
        "length target + unat pend_len + unat csz \<le> tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat pend_len.
           pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < pend_len"
      and data_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (of_nat j :: 32 word))"
      and data_pending_disj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (of_nat j :: 32 word)"
      and data_inj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat pend_len < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < pend_len \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec + pend_len). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj:
        "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.fused_C f = csz \<and>
                sections_result (fused_t_C.s_C f)
                  (sections_t_C.data_pos_C sec + pend_len)
                  (sections_t_C.inst_pos_C sec + 1)
                  (sections_t_C.addr_pos_C sec + an)
                  ENC_OK \<and>
                enc_sections_inv t data inst addr_buf (fused_t_C.s_C f)
                  src_seg tgt_len
                  (data_bytes @ heap_bytes_word s pending 0 pend_len)
                  (inst_bytes @ [ucast op])
                  (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
                  (copy_loop src_seg
                    (target @ heap_bytes_word s pending 0 pend_len)
                    (unat copy_addr) (unat csz))
                  (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?add = "heap_bytes_word s pending 0 pend_len"
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have mode_wf:
    "enc_mode_arg_wf c_out copy_addr here m"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
    using mode_le by (simp add: word_less_nat_alt word_le_nat_alt)
  have fop:
    "find_add_copy_opcode (length ?add) (unat csz)
       (unat (mode_t_C.mode_C m)) = Some (unat op)"
    unfolding csz_def op_def
    using add_copy_opcode_word_mode_le5_find_capped[
      OF pend_ge pend_le mode_le copy_ge]
    by simp
  have op_byte: "(word_of_nat (unat op) :: byte) = ucast op"
    by (rule byte_of_unat_ucast32)
  have here_eq_add:
    "unat here = length src_seg + length target + length ?add"
    using here_eq by simp
  have addr_ok_add:
    "unat copy_addr < length src_seg + length target + length ?add"
    using addr_ok by simp
  have target_room_add:
    "length target + length ?add + unat csz \<le> tgt_len"
    using target_room by simp
  have decodes_post:
    "section_decodes src_seg tgt_len
       (data_bytes @ ?add)
       (inst_bytes @ [ucast op])
       (addr_bytes @ varint_bytes32 (mode_t_C.arg_C m) an)
       (copy_loop src_seg (target @ ?add) (unat copy_addr) (unat csz))
       (cache_update c_out (unat copy_addr))"
    using section_decodes_fused_add_copy_append_varint_addr
      [OF enc_sections_invD(2)[OF inv] fop mode_wf mode_lt addr_size
          here_eq_add addr_ok_add target_room_add] op_byte
    by simp
  show ?thesis
    apply (rule runs_to_weaken[
      OF try_emit_add_copy'_mode_le5_success_emitted_sections
        [OF enc_sections_invD(1)[OF inv] bm pend_ge pend_le copy_ge
            mode_le addr_size sec_ok near_ptr_lt inst_byte_fits
            inst_byte_ptr inst_byte_dist inst_byte_data_disj
            inst_byte_addr_disj inst_byte_pending_disj data_fits data_valid
            pending_valid data_pending_disj data_inj data_prefix_disj
            data_no_overflow data_inst_disj data_addr_disj
            addr_varint_fits addr_varint_valid addr_varint_inj
            addr_varint_prefix_disj addr_varint_no_overflow
            addr_varint_data_disj addr_varint_inst_disj,
          folded csz_def op_def]])
    using decodes_post pend_ge pend_le copy_ge mode_le
    by (auto simp: enc_sections_inv_def csz_def op_def unat_word_ariths
                   word_less_nat_alt word_le_nat_alt)
qed

lemma try_emit_add_copy'_mode_le5_success_enc_sections_state_rel:
  fixes csz op pend_len copy_len :: "32 word"
    and m
  defines "csz \<equiv>
    (if (6 :: 32 word) < copy_len then (6 :: 32 word) else copy_len)"
    and "op \<equiv>
      (163 + mode_t_C.mode_C m * 12 + (pend_len - 1) * 3 + (csz - 4) ::
        32 word)"
  assumes rel:
        "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and pending_eq:
        "enc_pending spec_st = heap_bytes_word s pending 0 pend_len"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_len"
      and mode_le: "mode_t_C.mode_C m \<le> (5 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and addr_choice:
        "encode_address (enc_cache spec_st) (unat copy_addr)
           (src_len + enc_tp spec_st) =
         (unat (mode_t_C.mode_C m),
          varint_bytes32 (mode_t_C.arg_C m) an,
          cache_update (enc_cache spec_st) (unat copy_addr))"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_byte_dist:
        "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
      and inst_byte_data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr_buf +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_byte_pending_disj:
        "\<forall>i < unat pend_len.
           pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq>
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < pend_len"
      and data_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (of_nat j :: 32 word))"
      and data_pending_disj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (of_nat j :: 32 word)"
      and data_inj: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      and data_prefix_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_no_overflow:
        "unat (sections_t_C.data_pos_C sec) + unat pend_len < 2 ^ 32"
      and data_inst_disj: "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < pend_len \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_addr_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < pend_len \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj: "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_varint_data_disj: "\<forall>k < unat (sections_t_C.data_pos_C sec + pend_len). \<forall>i.
        i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_inst_disj:
        "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
        i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f spec_st'.
                r = Result f \<and>
                fused_t_C.fused_C f = csz \<and>
                try_emit_add_copy_spec src_len (unat copy_addr)
                  (unat copy_len) spec_st = Some spec_st' \<and>
                enc_sections_state_rel t data inst addr_buf
                  (fused_t_C.s_C f) spec_st') \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have pending_len: "length (enc_pending spec_st) = unat pend_len"
    using pending_eq by simp
  have spec_success:
    "try_emit_add_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st =
      Some (spec_st
        \<lparr> enc_tp := enc_tp spec_st + unat csz
         , enc_flushed := enc_flushed spec_st + unat pend_len + unat csz
         , enc_pending := []
         , enc_data := enc_data spec_st @ enc_pending spec_st
         , enc_inst := enc_inst spec_st @ [ucast op]
         , enc_addr := enc_addr spec_st @ varint_bytes32 (mode_t_C.arg_C m) an
         , enc_cache := cache_update (enc_cache spec_st) (unat copy_addr)
         , enc_trace := enc_trace spec_st
             @ [RAdd (enc_pending spec_st), RCopy (unat copy_addr) (unat csz)]
         \<rparr>)"
    unfolding csz_def op_def
    by (rule try_emit_add_copy_spec_mode_le5_success
      [OF pending_len pend_ge pend_le copy_ge mode_le addr_choice])
  show ?thesis
    apply (rule runs_to_weaken[
      OF try_emit_add_copy'_mode_le5_success_emitted_sections
        [OF enc_sections_state_relD(1)[OF rel] bm pend_ge pend_le copy_ge
            mode_le addr_size sec_ok near_ptr_lt inst_byte_fits
            inst_byte_ptr inst_byte_dist inst_byte_data_disj
            inst_byte_addr_disj inst_byte_pending_disj data_fits data_valid
            pending_valid data_pending_disj data_inj data_prefix_disj
            data_no_overflow data_inst_disj data_addr_disj
            addr_varint_fits addr_varint_valid addr_varint_inj
            addr_varint_prefix_disj addr_varint_no_overflow
            addr_varint_data_disj addr_varint_inst_disj,
          folded csz_def op_def]])
    using spec_success pending_eq
    by (auto simp: enc_sections_state_rel_def csz_def op_def
                   unat_word_ariths word_less_nat_alt word_le_nat_alt)
qed

(* The COPY/flush/fused section-decoder bridges above are ready to use when
   tightening the higher-level encoder preservation proofs. *)

end

end
