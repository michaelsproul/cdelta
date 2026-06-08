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


lemma buf_valid_near_arr_update[simp]:
  "buf_valid (near_arr_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma buf_valid_near_ptr_update[simp]:
  "buf_valid (near_ptr_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma buf_valid_same_arr_update[simp]:
  "buf_valid (same_arr_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma heap_bytes_near_arr_update[simp]:
  "heap_bytes (near_arr_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_near_ptr_update[simp]:
  "heap_bytes (near_ptr_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_same_arr_update[simp]:
  "heap_bytes (same_arr_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

end

end
