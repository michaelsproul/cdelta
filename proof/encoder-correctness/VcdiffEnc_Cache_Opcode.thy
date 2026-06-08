theory VcdiffEnc_Cache_Opcode
  imports
    VcdiffEnc_Writers
begin

context vcdiff_enc_global_addresses begin

lemma emit_address'_success_varint_heap_bytes_append:
  assumes mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and size: "varint_size' (mode_t_C.arg_C m) s = Some n"
      and fits: "\<not> addr_cap - addr_pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (addr_buf +\<^sub>p uint (addr_pos + of_nat j))"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           addr_buf +\<^sub>p uint (addr_pos + of_nat i) \<noteq>
           addr_buf +\<^sub>p uint (addr_pos + of_nat j)"
      and prefix_disj: "\<forall>k < unat addr_pos. \<forall>i.
           i < n \<longrightarrow> addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i)"
      and no_overflow: "unat addr_pos + unat n < 2 ^ 32"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
                   heap_bytes t addr_buf (unat (addr_pos + n)) =
                   heap_bytes s addr_buf (unat addr_pos) @
                   varint_bytes32 (mode_t_C.arg_C m) n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_address'_def
  using mode_lt
  apply simp
  by (rule write_varint'_success_heap_bytes_append_wordpos
      [OF size fits dst_valid dst_inj prefix_disj no_overflow])

lemma emit_address'_success_byte_heap_bytes_append:
  assumes mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and pos_lt: "addr_pos < addr_cap"
      and ptr_ok: "ptr_valid (heap_typing s) (addr_buf +\<^sub>p uint addr_pos)"
      and dist: "ptr_range_distinct addr_buf (Suc (unat addr_pos))"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
                   heap_bytes t addr_buf (unat (addr_pos + 1)) =
                   heap_bytes s addr_buf (unat addr_pos) @
                   [ucast (mode_t_C.arg_C m)] \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_address'_def
  using mode_ge
  apply simp
  by (rule write_byte'_heap_bytes_append_next_typing[OF pos_lt ptr_ok dist])

lemma single_add_opcode'_small:
  assumes sz_ge: "(1 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (17 :: 32 word)"
  shows "op_t_C.op_C (single_add_opcode' sz) = 1 + sz \<and>
         op_t_C.needs_size_C (single_add_opcode' sz) = 0"
  unfolding single_add_opcode'_def
  using sz_ge sz_le by simp

lemma single_add_opcode'_large:
  assumes sz_small: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
  shows "op_t_C.op_C (single_add_opcode' sz) = 1 \<and>
         op_t_C.needs_size_C (single_add_opcode' sz) = 1"
  unfolding single_add_opcode'_def
  using sz_small by simp

lemma single_copy_opcode'_small:
  assumes sz_ge: "(4 :: 32 word) \<le> sz"
      and sz_le: "sz \<le> (18 :: 32 word)"
  shows "op_t_C.op_C (single_copy_opcode' sz mode) =
           19 + mode * 16 - 3 + sz \<and>
         op_t_C.needs_size_C (single_copy_opcode' sz mode) = 0"
  unfolding single_copy_opcode'_def
  using sz_ge sz_le by simp

lemma single_copy_opcode'_large:
  assumes sz_large: "\<not> ((4 :: 32 word) \<le> sz \<and> sz \<le> (18 :: 32 word))"
  shows "op_t_C.op_C (single_copy_opcode' sz mode) = 19 + mode * 16 \<and>
         op_t_C.needs_size_C (single_copy_opcode' sz mode) = 1"
proof (cases "(4 :: 32 word) \<le> sz \<and> sz \<le> (18 :: 32 word)")
  case True
  show ?thesis
    using sz_large True by simp
next
  case False
  have guard_false:
    "\<not> ((4 :: 32 word) \<le> sz \<and> sz \<le> (0x12 :: 32 word))"
    using False by simp
  have guard_eq:
    "((4 :: 32 word) \<le> sz \<and> sz \<le> (0x12 :: 32 word)) = False"
    using guard_false by blast
  show ?thesis
    unfolding single_copy_opcode'_def Let_def
    by (simp add: guard_eq)
qed

lemma single_add_opcode'_find_single_add_opcode:
  "find_single_add_opcode (unat sz) =
    (unat (op_t_C.op_C (single_add_opcode' sz)),
     op_t_C.needs_size_C (single_add_opcode' sz) \<noteq> 0)"
  unfolding single_add_opcode'_def find_single_add_opcode_def
  by (auto simp: word_le_nat_alt unat_word_ariths)

lemma single_add_opcode'_default_entry:
  "default_entry (unat (op_t_C.op_C (single_add_opcode' sz))) =
    (add_hi (if op_t_C.needs_size_C (single_add_opcode' sz) = 0 then unat sz else 0),
     noop_hi)"
proof (cases "(1 :: 32 word) \<le> sz \<and> sz \<le> 17")
  case True
  then have sz_nat: "1 \<le> unat sz" "unat sz \<le> 17"
    by (simp_all add: word_le_nat_alt)
  then show ?thesis
    using True default_entry_add_small[OF sz_nat]
    by (simp add: single_add_opcode'_def unat_word_ariths)
next
  case False
  then show ?thesis
    by (auto simp: single_add_opcode'_def default_entry_def add_hi_def noop_hi_def)
qed

lemma single_copy_opcode'_find_single_copy_opcode:
  assumes mode_le: "mode \<le> (8 :: 32 word)"
  shows "find_single_copy_opcode (unat sz) (unat mode) =
    (unat (op_t_C.op_C (single_copy_opcode' sz mode)),
     op_t_C.needs_size_C (single_copy_opcode' sz mode) \<noteq> 0)"
proof (cases "(4 :: 32 word) \<le> sz \<and> sz \<le> 18")
  case True
  then have sz_nat: "4 \<le> unat sz" "unat sz \<le> 18"
    by (simp_all add: word_le_nat_alt)
  have mode_nat: "unat mode \<le> 8"
    using mode_le by (simp add: word_le_nat_alt)
  have op_unat:
    "unat (19 + mode * 16 - 3 + sz :: 32 word) =
     19 + unat mode * 16 + unat sz - 3"
    using True mode_nat
    by (simp add: word_le_nat_alt unat_word_ariths)
  show ?thesis
    using True sz_nat op_unat
    by (simp add: single_copy_opcode'_def find_single_copy_opcode_def Let_def)
next
  case False
  have mode_nat: "unat mode \<le> 8"
    using mode_le by (simp add: word_le_nat_alt)
  have op_unat:
    "unat (19 + mode * 16 :: 32 word) = 19 + unat mode * 16"
    using mode_nat by (simp add: unat_word_ariths)
  show ?thesis
    using False op_unat
    by (auto simp: single_copy_opcode'_def find_single_copy_opcode_def Let_def
              word_le_nat_alt)
qed

lemma single_copy_opcode'_default_entry:
  assumes mode_le: "mode \<le> (8 :: 32 word)"
  shows "default_entry (unat (op_t_C.op_C (single_copy_opcode' sz mode))) =
    (copy_hi (if op_t_C.needs_size_C (single_copy_opcode' sz mode) = 0 then unat sz else 0)
             (unat mode),
     noop_hi)"
proof (cases "(4 :: 32 word) \<le> sz \<and> sz \<le> 18")
  case True
  then have sz_nat: "4 \<le> unat sz" "unat sz \<le> 18"
    by (simp_all add: word_le_nat_alt)
  have mode_nat: "unat mode \<le> 8"
    using mode_le by (simp add: word_le_nat_alt)
  have op_unat:
    "unat (19 + mode * 16 - 3 + sz :: 32 word) =
     19 + unat mode * 16 + unat sz - 3"
    using True mode_nat
    by (simp add: word_le_nat_alt unat_word_ariths)
  show ?thesis
    using True default_entry_copy_small[OF mode_nat sz_nat] op_unat
    by (simp add: single_copy_opcode'_def)
next
  case False
  have mode_nat: "unat mode \<le> 8"
    using mode_le by (simp add: word_le_nat_alt)
  have op_unat:
    "unat (19 + mode * 16 :: 32 word) = 19 + unat mode * 16"
    using mode_nat by (simp add: unat_word_ariths)
  show ?thesis
    using False default_entry_copy_varint[OF mode_nat] op_unat
    by (auto simp: single_copy_opcode'_def Let_def)
qed

lemma add_copy_opcode_word_mode_le5_default_entry:
  assumes add_ge: "(1 :: 32 word) \<le> add_sz"
      and add_le: "add_sz \<le> (4 :: 32 word)"
      and mode_le: "mode \<le> (5 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_sz"
      and copy_le: "copy_sz \<le> (6 :: 32 word)"
  shows "default_entry
          (unat (163 + mode * 12 + (add_sz - 1) * 3 + (copy_sz - 4) :: 32 word)) =
         (add_hi (unat add_sz), copy_hi (unat copy_sz) (unat mode))"
proof -
  have pure_ranges:
    "1 \<le> unat add_sz" "unat add_sz \<le> 4"
    "unat mode \<le> 5 \<and> 4 \<le> unat copy_sz \<and> unat copy_sz \<le> 6"
    using assms by (simp_all add: word_le_nat_alt)
  have find:
    "find_add_copy_opcode (unat add_sz) (unat copy_sz) (unat mode) =
     Some (unat (163 + mode * 12 + (add_sz - 1) * 3 + (copy_sz - 4) :: 32 word))"
    using assms
    by (simp add: find_add_copy_opcode_def word_le_nat_alt unat_word_ariths)
  obtain op where
    op_find: "find_add_copy_opcode (unat add_sz) (unat copy_sz) (unat mode) = Some op"
    and op_entry:
      "default_entry op = (add_hi (unat add_sz), copy_hi (unat copy_sz) (unat mode))"
    using default_entry_add_copy[OF pure_ranges(1) pure_ranges(2)] pure_ranges(3)
    by blast
  show ?thesis
    using find op_find op_entry by simp
qed

lemma add_copy_opcode_word_mode_gt5_default_entry:
  assumes add_ge: "(1 :: 32 word) \<le> add_sz"
      and add_le: "add_sz \<le> (4 :: 32 word)"
      and mode_gt: "(5 :: 32 word) < mode"
      and mode_le: "mode \<le> (8 :: 32 word)"
      and copy_eq: "copy_sz = (4 :: 32 word)"
  shows "default_entry
          (unat (235 + (mode - 6) * 4 + (add_sz - 1) :: 32 word)) =
         (add_hi (unat add_sz), copy_hi (unat copy_sz) (unat mode))"
proof -
  have pure_ranges:
    "1 \<le> unat add_sz" "unat add_sz \<le> 4"
    "6 \<le> unat mode \<and> unat mode \<le> 8 \<and> unat copy_sz = 4"
    using assms by (auto simp: word_le_nat_alt word_less_nat_alt)
  have find:
    "find_add_copy_opcode (unat add_sz) (unat copy_sz) (unat mode) =
     Some (unat (235 + (mode - 6) * 4 + (add_sz - 1) :: 32 word))"
    using assms
    by (simp add: find_add_copy_opcode_def word_le_nat_alt word_less_nat_alt
                  unat_word_ariths)
  obtain op where
    op_find: "find_add_copy_opcode (unat add_sz) (unat copy_sz) (unat mode) = Some op"
    and op_entry:
      "default_entry op = (add_hi (unat add_sz), copy_hi (unat copy_sz) (unat mode))"
    using default_entry_add_copy[OF pure_ranges(1) pure_ranges(2)] pure_ranges(3)
    by blast
  show ?thesis
    using find op_find op_entry by simp
qed

lemma add_copy_opcode'_mode_le5:
  assumes add_ge: "(1 :: 32 word) \<le> add_sz"
      and add_le: "add_sz \<le> (4 :: 32 word)"
      and mode_le: "mode \<le> (5 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_sz"
      and copy_le: "copy_sz \<le> (6 :: 32 word)"
  shows "add_copy_opcode' add_sz copy_sz mode \<bullet> s
           \<lbrace> \<lambda>r t. r = Result
                (163 + mode * 12 + (add_sz - 1) * 3 + (copy_sz - 4)) \<and>
                   t = s \<rbrace>"
  unfolding add_copy_opcode'_def
  apply runs_to_vcg
  using assms by auto

lemma add_copy_opcode'_mode_gt5:
  assumes add_ge: "(1 :: 32 word) \<le> add_sz"
      and add_le: "add_sz \<le> (4 :: 32 word)"
      and mode_gt: "(5 :: 32 word) < mode"
      and mode_le: "mode \<le> (8 :: 32 word)"
      and copy_eq: "copy_sz = (4 :: 32 word)"
  shows "add_copy_opcode' add_sz copy_sz mode \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (235 + (mode - 6) * 4 + (add_sz - 1)) \<and>
                   t = s \<rbrace>"
  unfolding add_copy_opcode'_def
  apply runs_to_vcg
  using assms by auto

lemma add_copy_opcode'_zero:
  assumes "\<not> ((1 :: 32 word) \<le> add_sz \<and> add_sz \<le> 4 \<and>
              ((mode \<le> 5 \<and> 4 \<le> copy_sz \<and> copy_sz \<le> 6) \<or>
               (5 < mode \<and> mode \<le> 8 \<and> copy_sz = 4)))"
  shows "add_copy_opcode' add_sz copy_sz mode \<bullet> s
           \<lbrace> \<lambda>r t. r = Result 0 \<and> t = s \<rbrace>"
  unfolding add_copy_opcode'_def
  apply runs_to_vcg
  using assms by (auto simp: word_le_nat_alt word_less_nat_alt word_neq_0_conv)

lemma varint_decode_varint_bytes32_unat:
  assumes size: "varint_size' v s = Some n"
  shows "varint_decode (varint_bytes32 v n @ rest) = Some (unat v, rest)"
  using varint_decode_varint_bytes32[OF size, of rest] .


lemma buf_valid_near_arr_update[simp]:
  "buf_valid (near_arr_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma buf_valid_near_ptr_update[simp]:
  "buf_valid (near_ptr_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma buf_valid_same_arr_update[simp]:
  "buf_valid (same_arr_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma heap_typing_near_arr_update[simp]:
  "heap_typing (near_arr_''_update f s) = heap_typing s"
  by simp

lemma heap_typing_near_ptr_update[simp]:
  "heap_typing (near_ptr_''_update f s) = heap_typing s"
  by simp

lemma heap_typing_same_arr_update[simp]:
  "heap_typing (same_arr_''_update f s) = heap_typing s"
  by simp

lemma ptr_valid_near_arr_update[simp]:
  "ptr_valid (heap_typing (near_arr_''_update f s)) p = ptr_valid (heap_typing s) p"
  by simp

lemma ptr_valid_near_ptr_update[simp]:
  "ptr_valid (heap_typing (near_ptr_''_update f s)) p = ptr_valid (heap_typing s) p"
  by simp

lemma ptr_valid_same_arr_update[simp]:
  "ptr_valid (heap_typing (same_arr_''_update f s)) p = ptr_valid (heap_typing s) p"
  by simp

lemma heap_bytes_near_arr_update[simp]:
  "heap_bytes (near_arr_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_near_ptr_update[simp]:
  "heap_bytes (near_ptr_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_same_arr_update[simp]:
  "heap_bytes (same_arr_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma cache_update'_state:
  assumes near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
  shows "cache_update' addr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               near_arr_'' t =
                 Arrays.update (near_arr_'' s) (unat (near_ptr_'' s)) addr \<and>
               near_ptr_'' t = (near_ptr_'' s + 1) mod 4 \<and>
               same_arr_'' t =
                 Arrays.update (same_arr_'' s) (unat (addr mod 0x300)) addr \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t buf n = heap_bytes s buf n \<rbrace>"
  unfolding cache_update'_def
  apply runs_to_vcg
  using near_ptr_lt by (auto simp: word_less_nat_alt unat_mod)

lemma cache_update'_preserves_heap_bytes:
  assumes near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
  shows "cache_update' addr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t buf n = heap_bytes s buf n \<rbrace>"
  apply (rule runs_to_weaken[OF cache_update'_state[OF near_ptr_lt, where buf = buf and n = n]])
  by simp

end

end
