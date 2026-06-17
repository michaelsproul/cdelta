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

lemma flush_pending_spec_empty_sections:
  assumes pending_empty: "enc_pending st = []"
  shows "enc_data (flush_pending_spec src_len st) = enc_data st"
    and "enc_inst (flush_pending_spec src_len st) = enc_inst st"
    and "enc_addr (flush_pending_spec src_len st) = enc_addr st"
  using pending_empty
  by (simp_all add: flush_pending_spec_def flush_pending_insts_def
                    emit_insts_spec_def append_add_inst_def
                    close_pending_run_def pending_scan_init_def)

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

lemma foldl_pending_scan_step_replicate_current:
  assumes run_byte: "ps_run_byte s = Some b"
  shows "foldl pending_scan_step s (replicate n b) =
   s\<lparr>ps_run_len := ps_run_len s + n\<rparr>"
  using run_byte
  by (induction n arbitrary: s)
     (simp_all add: pending_scan_step_def ac_simps)

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

lemma runs_to_liftE_bind_throw_result:
  assumes f: "f \<bullet> s \<lbrace>\<lambda>Res v t. P v t\<rbrace>"
  shows "(liftE f >>= throw) \<bullet> s
           \<lbrace>\<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> Q v t) \<and>
                   (\<forall>v. r = Exn v \<longrightarrow> P v t)\<rbrace>"
  apply runs_to_vcg
  apply (rule runs_to_weaken[OF f])
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
     apply (rule emit_run'_success_enc_sections_state_rel[
        where src_len = src_len and n = n])
                       apply (rule rel)
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
    using pure_sections
    apply (clarsimp simp: enc_sections_state_rel_def sections_result_def)
    apply runs_to_vcg
    apply (subst whileLoop_unroll)
    apply runs_to_vcg
    done
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
  show ?thesis
    apply (rule runs_to_bind_exception)
    apply (rule runs_to_weaken[
      OF flush_pending'_replicate_run_prescan_two_condition_liftE[
        OF len_gt2 pending_all_eq pending_valid]])
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken)
     apply (rule emit_run'_success_enc_sections_state_rel[
        where src_len = src_len and n = n])
                       apply (rule rel)
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
       apply (rule emit_run'_success_enc_sections_state_rel[
          where src_len = src_len and n = n])
                         apply (rule rel)
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
       apply (rule emit_run'_success_enc_sections_state_rel[
          where src_len = src_len and n = n])
                         apply (rule rel)
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

(* Nontrivial COPY/flush/fused preservation needs these shared facts:
   best_mode'_encode_address_correct for the C cache state,
   section_decodes_copy_append,
   section_decodes_flush_pending_add_run_chunks, and
   section_decodes_fused_add_copy_append. *)

end

end
