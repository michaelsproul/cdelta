theory VcdiffEnc_Cache_Opcode
  imports
    VcdiffEnc_Writers
begin

context vcdiff_enc_global_addresses begin

lemma byte_of_unat_ucast32:
  "(word_of_nat (unat (w :: 32 word)) :: byte) = ucast w"
  by (simp add: word_unat.Rep_inverse)

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

lemma emit_address'_success_varint_heap_bytes_append_preserves2:
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
      and disj1: "\<forall>k < out1_n. \<forall>i.
           i < n \<longrightarrow> out1 +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i)"
      and disj2: "\<forall>k < out2_n. \<forall>i.
           i < n \<longrightarrow> out2 +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i)"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
                   heap_bytes t addr_buf (unat (addr_pos + n)) =
                   heap_bytes s addr_buf (unat addr_pos) @
                   varint_bytes32 (mode_t_C.arg_C m) n \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_address'_def
  using mode_lt
  apply simp
  by (rule write_varint'_success_heap_bytes_append_wordpos_preserves2
      [OF size fits dst_valid dst_inj prefix_disj no_overflow disj1 disj2])

lemma emit_address'_success_varint_heap_bytes_append_preserves2_near_ptr:
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
      and disj1: "\<forall>k < out1_n. \<forall>i.
           i < n \<longrightarrow> out1 +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i)"
      and disj2: "\<forall>k < out2_n. \<forall>i.
           i < n \<longrightarrow> out2 +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i)"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
                   heap_bytes t addr_buf (unat (addr_pos + n)) =
                   heap_bytes s addr_buf (unat addr_pos) @
                   varint_bytes32 (mode_t_C.arg_C m) n \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   near_ptr_'' t = near_ptr_'' s \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_address'_def
  using mode_lt
  apply simp
  by (rule write_varint'_success_heap_bytes_append_wordpos_preserves2_near_ptr
      [OF size fits dst_valid dst_inj prefix_disj no_overflow disj1 disj2])

lemma emit_address'_success_byte_heap_bytes_append_preserves2:
  assumes mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and pos_lt: "addr_pos < addr_cap"
      and ptr_ok: "ptr_valid (heap_typing s) (addr_buf +\<^sub>p uint addr_pos)"
      and dist: "ptr_range_distinct addr_buf (Suc (unat addr_pos))"
      and disj1: "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint addr_pos"
      and disj2: "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint addr_pos"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
                   heap_bytes t addr_buf (unat (addr_pos + 1)) =
                   heap_bytes s addr_buf (unat addr_pos) @
                   [ucast (mode_t_C.arg_C m)] \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_address'_def
  using mode_ge
  apply simp
  by (rule write_byte'_heap_bytes_append_next_typing_preserves2
      [OF pos_lt ptr_ok dist disj1 disj2])

lemma emit_address'_success_byte_heap_bytes_append_preserves2_near_ptr:
  assumes mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and pos_lt: "addr_pos < addr_cap"
      and ptr_ok: "ptr_valid (heap_typing s) (addr_buf +\<^sub>p uint addr_pos)"
      and dist: "ptr_range_distinct addr_buf (Suc (unat addr_pos))"
      and disj1: "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint addr_pos"
      and disj2: "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint addr_pos"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
                   heap_bytes t addr_buf (unat (addr_pos + 1)) =
                   heap_bytes s addr_buf (unat addr_pos) @
                   [ucast (mode_t_C.arg_C m)] \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   near_ptr_'' t = near_ptr_'' s \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append2:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
               heap_bytes t addr_buf (unat (addr_pos + 1)) =
               heap_bytes s addr_buf (unat addr_pos) @
               [ucast (mode_t_C.arg_C m)] \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_address'_success_byte_heap_bytes_append_preserves2
      [OF mode_ge pos_lt ptr_ok dist disj1 disj2])
  have near:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
               near_ptr_'' t = near_ptr_'' s \<and>
               heap_typing t = heap_typing s \<rbrace>"
    unfolding emit_address'_def
    using mode_ge
    apply simp
    apply (rule runs_to_weaken[OF write_byte'_spec])
     apply (rule ptr_ok)
    using pos_lt by auto
  have combined:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
           heap_bytes t addr_buf (unat (addr_pos + 1)) =
           heap_bytes s addr_buf (unat addr_pos) @
           [ucast (mode_t_C.arg_C m)] \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
           near_ptr_'' t = near_ptr_'' s \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append2 near by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

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

lemma add_copy_opcode_word_mode_le5_find:
  assumes add_ge: "(1 :: 32 word) \<le> add_sz"
      and add_le: "add_sz \<le> (4 :: 32 word)"
      and mode_le: "mode \<le> (5 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_sz"
      and copy_le: "copy_sz \<le> (6 :: 32 word)"
  shows "find_add_copy_opcode (unat add_sz) (unat copy_sz) (unat mode) =
         Some (unat (163 + mode * 12 + (add_sz - 1) * 3 + (copy_sz - 4) :: 32 word))"
  using assms
  by (simp add: find_add_copy_opcode_def word_le_nat_alt unat_word_ariths)

lemma add_copy_opcode_word_mode_le5_find_capped:
  fixes add_sz copy_sz mode csz :: "32 word"
  defines "csz \<equiv> (if (6 :: 32 word) < copy_sz then (6 :: 32 word) else copy_sz)"
  assumes add_ge: "(1 :: 32 word) \<le> add_sz"
      and add_le: "add_sz \<le> (4 :: 32 word)"
      and mode_le: "mode \<le> (5 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_sz"
  shows "find_add_copy_opcode (unat add_sz) (unat csz) (unat mode) =
         Some (unat (163 + mode * 12 + (add_sz - 1) * 3 + (csz - 4) :: 32 word))"
proof -
  have csz_range: "(4 :: 32 word) \<le> csz" "csz \<le> (6 :: 32 word)"
    using copy_ge unfolding csz_def
    by (auto simp: word_less_nat_alt word_le_nat_alt)
  show ?thesis
    by (rule add_copy_opcode_word_mode_le5_find[OF add_ge add_le mode_le csz_range])
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

lemma add_copy_opcode_word_mode_gt5_find:
  assumes add_ge: "(1 :: 32 word) \<le> add_sz"
      and add_le: "add_sz \<le> (4 :: 32 word)"
      and mode_gt: "(5 :: 32 word) < mode"
      and mode_le: "mode \<le> (8 :: 32 word)"
      and copy_eq: "copy_sz = (4 :: 32 word)"
  shows "find_add_copy_opcode (unat add_sz) (unat copy_sz) (unat mode) =
         Some (unat (235 + (mode - 6) * 4 + (add_sz - 1) :: 32 word))"
  using assms
  by (simp add: find_add_copy_opcode_def word_le_nat_alt word_less_nat_alt
                unat_word_ariths)

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

lemma varint_size'_neq_None:
  "varint_size' v s \<noteq> None"
  using varint_size'_some[of v s] by auto

lemma enc_oreturn_apply[simp]:
  "oreturn x s = Some x"
  by (simp add: oreturn_def K_def)

definition enc_cache_abs :: "lifted_globals \<Rightarrow> cache \<Rightarrow> bool" where
  "enc_cache_abs s c \<longleftrightarrow>
     length (near c) = s_near \<and>
     length (same c) = same_buckets \<and>
     unat (near_ptr_'' s) < s_near \<and>
     near_ptr c = unat (near_ptr_'' s) \<and>
     (\<forall>i < s_near. near_arr_'' s .[i] = of_nat (near c ! i)) \<and>
     (\<forall>i < same_buckets. same_arr_'' s .[i] = of_nat (same c ! i))"

definition enc_cache_wf :: "cache \<Rightarrow> bool" where
  "enc_cache_wf c \<longleftrightarrow>
     length (near c) = s_near \<and>
     length (same c) = same_buckets \<and>
     near_ptr c < s_near \<and>
     (\<forall>i < s_near. near c ! i < 2 ^ 32) \<and>
     (\<forall>i < same_buckets. same c ! i < 2 ^ 32)"

lemma heap_typing_heap_w8_update[simp]:
  "heap_typing (heap_w8_update f s) = heap_typing s"
  by simp

lemma enc_cache_abs_heap_w8_update[simp]:
  "enc_cache_abs (heap_w8_update f s) c = enc_cache_abs s c"
  by (simp add: enc_cache_abs_def)

lemma enc_cache_wf_cache_init[simp]:
  "enc_cache_wf cache_init"
proof -
  have near_bound: "\<forall>i < s_near. near cache_init ! i < 2 ^ 32"
    by (simp add: enc_cache_wf_def cache_init_def nth_replicate)
  have same_bound: "\<forall>i < same_buckets. same cache_init ! i < 2 ^ 32"
    by (simp add: enc_cache_wf_def cache_init_def nth_replicate)
  show ?thesis
    using near_bound same_bound
    by (simp add: enc_cache_wf_def cache_init_def)
qed

lemma enc_cache_wf_update:
  assumes wf: "enc_cache_wf c"
      and addr_lt: "addr < 2 ^ 32"
  shows "enc_cache_wf (cache_update c addr)"
  using wf addr_lt
  unfolding enc_cache_wf_def cache_update_def
  by (auto simp: nth_list_update split: if_splits)

lemma enc_cache_abs_near_ptr_lt_word:
  assumes "enc_cache_abs s c"
  shows "near_ptr_'' s < (4 :: 32 word)"
  using assms by (simp add: enc_cache_abs_def s_near_def word_less_nat_alt)

lemma enc_cache_abs_near_unat:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and i_lt: "i < s_near"
  shows "unat (near_arr_'' s .[i]) = near c ! i"
proof -
  have arr_eq: "near_arr_'' s .[i] = (of_nat (near c ! i) :: 32 word)"
    using abs i_lt by (simp add: enc_cache_abs_def)
  have val_lt: "near c ! i < 2 ^ 32"
    using wf i_lt by (simp add: enc_cache_wf_def)
  show ?thesis
    using arr_eq val_lt by (simp add: unat_of_nat_eq)
qed

lemma enc_cache_abs_same_unat:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and i_lt: "i < same_buckets"
  shows "unat (same_arr_'' s .[i]) = same c ! i"
proof -
  have arr_eq: "same_arr_'' s .[i] = (of_nat (same c ! i) :: 32 word)"
    using abs i_lt by (simp add: enc_cache_abs_def)
  have val_lt: "same c ! i < 2 ^ 32"
    using wf i_lt by (simp add: enc_cache_wf_def)
  show ?thesis
    using arr_eq val_lt by (simp add: unat_of_nat_eq)
qed

lemma enc_cache_abs_cache_initI:
  assumes np: "near_ptr_'' s = 0"
      and near_zero: "\<forall>i < (4 :: nat). near_arr_'' s .[i] = (0 :: 32 word)"
      and same_zero: "\<forall>i < (768 :: nat). same_arr_'' s .[i] = (0 :: 32 word)"
  shows "enc_cache_abs s cache_init"
proof -
  have near_len: "length (near cache_init) = s_near"
    by (simp add: cache_init_def)
  have same_len: "length (same cache_init) = same_buckets"
    by (simp add: cache_init_def)
  have near_contents:
    "\<forall>i < s_near. near_arr_'' s .[i] = of_nat (near cache_init ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < s_near"
    have i_lt_4: "i < 4"
      using i_lt by (simp add: s_near_def)
    have "near cache_init ! i = 0"
      using i_lt by (simp add: cache_init_def nth_replicate)
    then show "near_arr_'' s .[i] = of_nat (near cache_init ! i)"
      using near_zero i_lt_4 by simp
  qed
  have same_contents:
    "\<forall>i < same_buckets. same_arr_'' s .[i] = of_nat (same cache_init ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < same_buckets"
    have i_lt_768: "i < 768"
      using i_lt by (simp add: same_buckets_def s_same_def)
    have "same cache_init ! i = 0"
      using i_lt by (simp add: cache_init_def nth_replicate)
    then show "same_arr_'' s .[i] = of_nat (same cache_init ! i)"
      using same_zero i_lt_768 by simp
  qed
  show ?thesis
    using np near_len same_len near_contents same_contents
    by (simp add: enc_cache_abs_def cache_init_def)
qed

lemma enc_cache_abs_update_state:
  assumes abs: "enc_cache_abs s c"
      and np_lt: "near_ptr_'' s < (4 :: 32 word)"
  shows "enc_cache_abs
           (same_arr_''_update
              (\<lambda>a. Arrays.update a (unat (w mod 0x300 :: 32 word)) w)
              (near_ptr_''_update
                (\<lambda>_. (near_ptr_'' s + 1) mod (4 :: 32 word))
                (near_arr_''_update
                  (\<lambda>a. Arrays.update a (unat (near_ptr_'' s)) w) s)))
           (cache_update c (unat w))"
proof -
  let ?sb = "same_buckets"
  let ?addr = "unat w"
  let ?np = "near_ptr_'' s"
  let ?np' = "(?np + 1) mod (4 :: 32 word)"
  let ?slot_w = "w mod 0x300 :: 32 word"
  let ?slot_n = "unat ?slot_w"
  let ?s' = "same_arr_''_update
              (\<lambda>a. Arrays.update a ?slot_n w)
              (near_ptr_''_update (\<lambda>_. ?np')
                (near_arr_''_update
                  (\<lambda>a. Arrays.update a (unat ?np) w) s))"
  let ?c' = "cache_update c ?addr"

  have len_near: "length (near c) = s_near"
    using abs by (simp add: enc_cache_abs_def)
  have len_same: "length (same c) = ?sb"
    using abs by (simp add: enc_cache_abs_def)
  have np_eq: "near_ptr c = unat ?np"
    using abs by (simp add: enc_cache_abs_def)
  have np_lt_sn: "unat ?np < s_near"
    using abs by (simp add: enc_cache_abs_def)
  have s_near_4: "s_near = 4"
    by (simp add: s_near_def)
  have sb_768: "?sb = 768"
    by (simp add: same_buckets_def s_same_def)
  have near_i: "\<forall>i. i < s_near \<longrightarrow> near_arr_'' s .[i] = of_nat (near c ! i)"
    using abs by (simp add: enc_cache_abs_def)
  have same_i: "\<forall>i. i < ?sb \<longrightarrow> same_arr_'' s .[i] = of_nat (same c ! i)"
    using abs by (simp add: enc_cache_abs_def)

  have np_plus_1: "unat (?np + 1) = unat ?np + 1"
    using unat_word_suc_of_less[OF np_lt] by simp
  have np'_eq: "unat ?np' = (unat ?np + 1) mod 4"
    by (simp add: unat_mod np_plus_1)
  have np'_lt_sn: "unat ?np' < s_near"
    using np'_eq s_near_4 by simp
  have np'_eq_nearptr: "near_ptr ?c' = unat ?np'"
    by (simp add: cache_update_def np'_eq s_near_4 np_eq)

  have near_len_new: "length (near ?c') = s_near"
    by (simp add: cache_update_def len_near)
  have same_len_new: "length (same ?c') = ?sb"
    by (simp add: cache_update_def len_same)

  have near_slot_lt: "unat ?np < CARD(4)"
    using np_lt_sn s_near_4 by simp
  have near_arr_new:
    "near_arr_'' ?s' = Arrays.update (near_arr_'' s) (unat ?np) w"
    by simp
  have near_contents:
    "\<forall>i. i < s_near \<longrightarrow> near_arr_'' ?s' .[i] = of_nat (near ?c' ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < s_near"
    have i_lt_4: "i < CARD(4)"
      using i_lt s_near_4 by simp
    show "near_arr_'' ?s' .[i] = of_nat (near ?c' ! i)"
    proof (cases "i = unat ?np")
      case True
      have "near_arr_'' ?s' .[i] = w"
        using True near_slot_lt near_arr_new
        by (simp add: Arrays.index_update i_lt_4)
      also have "\<dots> = of_nat (near ?c' ! i)"
        using True np_eq len_near np_lt_sn
        by (simp add: cache_update_def nth_list_update_eq)
      finally show ?thesis .
    next
      case False
      have "near_arr_'' ?s' .[i] = near_arr_'' s .[i]"
        using False near_arr_new i_lt_4
        by (simp add: index_update2)
      also have "\<dots> = of_nat (near c ! i)"
        using i_lt near_i by auto
      also have "\<dots> = of_nat (near ?c' ! i)"
        using False np_eq
        by (simp add: cache_update_def nth_list_update_neq)
      finally show ?thesis .
    qed
  qed

  have slot_w_eq_n: "?slot_n = ?addr mod ?sb"
    by (simp add: unat_mod sb_768)
  have slot_n_lt_sb: "?slot_n < ?sb"
    by (simp add: slot_w_eq_n sb_768)
  have slot_n_lt_768: "?slot_n < CARD(768)"
    using slot_n_lt_sb sb_768 by simp
  have same_arr_new:
    "same_arr_'' ?s' = Arrays.update (same_arr_'' s) ?slot_n w"
    by simp
  have same_contents:
    "\<forall>i. i < ?sb \<longrightarrow> same_arr_'' ?s' .[i] = of_nat (same ?c' ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < ?sb"
    have i_lt_768: "i < CARD(768)"
      using i_lt sb_768 by simp
    show "same_arr_'' ?s' .[i] = of_nat (same ?c' ! i)"
    proof (cases "i = ?slot_n")
      case True
      have "same_arr_'' ?s' .[i] = w"
        using True slot_n_lt_768 same_arr_new
        by (simp add: index_update)
      also have "\<dots> = of_nat (same ?c' ! i)"
        using True slot_w_eq_n len_same slot_n_lt_sb
        by (simp add: cache_update_def nth_list_update_eq)
      finally show ?thesis .
    next
      case False
      have "same_arr_'' ?s' .[i] = same_arr_'' s .[i]"
        using False same_arr_new slot_n_lt_768 i_lt_768
        by (simp add: index_update2)
      also have "\<dots> = of_nat (same c ! i)"
        using i_lt same_i by auto
      also have "\<dots> = of_nat (same ?c' ! i)"
        using False slot_w_eq_n
        by (simp add: cache_update_def nth_list_update_neq)
      finally show ?thesis .
    qed
  qed

  show ?thesis
    unfolding enc_cache_abs_def
    using near_len_new same_len_new np'_lt_sn np'_eq_nearptr
          near_contents same_contents
    by simp
qed


lemma near_reset_loop_zeros_word:
  "(whileLoop (\<lambda>idx st. idx < (4 :: 32 word))
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word)
          \<and> (\<forall>i < (4::nat). near_arr_'' t .[i] = (0 :: 32 word))
          \<and> same_arr_'' t = same_arr_'' s0
          \<and> near_ptr_'' t = near_ptr_'' s0
          \<and> heap_typing t = heap_typing s0
          \<and> heap_bytes t buf n = heap_bytes s0 buf n \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 4 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 4
              \<and> (\<forall>i < unat idx. near_arr_'' st .[i] = (0 :: 32 word))
              \<and> same_arr_'' st = same_arr_'' s0
              \<and> near_ptr_'' st = near_ptr_'' s0
              \<and> heap_typing st = heap_typing s0
              \<and> heap_bytes st buf n = heap_bytes s0 buf n"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt unat_word_ariths(1) heap_bytes_def)
    subgoal for i
      apply (cases "i = unat idx")
       apply simp
      apply (subgoal_tac "i < unat idx")
       apply simp
      apply (simp add: less_Suc_eq)
      done
    done
  done

lemma same_reset_loop_zeros_word:
  "(whileLoop (\<lambda>idx st. idx < (0x300 :: 32 word))
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (0x300 :: 32 word)
          \<and> (\<forall>i < (768::nat). same_arr_'' t .[i] = (0 :: 32 word))
          \<and> near_arr_'' t = near_arr_'' s0
          \<and> near_ptr_'' t = near_ptr_'' s0
          \<and> heap_typing t = heap_typing s0
          \<and> heap_bytes t buf n = heap_bytes s0 buf n \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 768 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 768
              \<and> (\<forall>i < unat idx. same_arr_'' st .[i] = (0 :: 32 word))
              \<and> near_arr_'' st = near_arr_'' s0
              \<and> near_ptr_'' st = near_ptr_'' s0
              \<and> heap_typing st = heap_typing s0
              \<and> heap_bytes st buf n = heap_bytes s0 buf n"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt unat_word_ariths(1) heap_bytes_def)
    subgoal for i
      apply (cases "i = unat idx")
       apply simp
      apply (subgoal_tac "i < unat idx")
       apply simp
      apply (simp add: less_Suc_eq)
      done
    done
  done


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

lemma write_byte'_success_preserves_enc_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   enc_cache_abs t c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[OF write_byte'_spec])
   using ptr_ok apply simp
  using assms by auto

lemma write_bytes_loop_preserves_enc_cache_abs:
  fixes len pos src_off :: "32 word"
  assumes abs: "enc_cache_abs s c"
      and dst_valid: "\<forall>j < unat len.
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
            enc_cache_abs t c \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len \<and>
             enc_cache_abs st c \<and>
             heap_typing st = heap_typing s"])
     subgoal by simp
    subgoal using abs by simp
   subgoal premises prems for i st
   proof -
     have len_le: "unat len \<le> unat i"
       using prems(1) by (simp add: word_less_nat_alt)
     have i_eq: "i = len"
       using prems(2) len_le by (metis antisym_conv word_unat.Rep_inject)
     show ?thesis
       using prems(2) i_eq by simp
   qed
  subgoal premises prems for i st
  proof -
    have i_word: "i < len"
      using prems(1) by (simp add: word_less_nat_alt)
    have i_lt: "unat i < unat len"
      using i_word by (simp add: word_less_nat_alt)
    have i_of_nat: "(of_nat (unat i) :: 32 word) = i"
      by (simp add: word_unat.Rep_inverse)
    have dst:
      "ptr_valid (heap_typing st) (buf +\<^sub>p uint (pos + i))"
      using dst_valid[rule_format, of "unat i"] i_lt prems(2)
      by (simp add: i_of_nat)
    have src_ptr:
      "ptr_valid (heap_typing st) (src +\<^sub>p uint (src_off + i))"
      using src_valid[rule_format, of "unat i"] i_lt prems(2)
      by (simp add: i_of_nat)
    show ?thesis
      using prems dst src_ptr i_word
      by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                     word_less_nat_alt word_unat.Rep_inverse
               intro: unat_suc_le_of_word_less
                      unat_measure_decrease_of_word_less)
  qed
  done

lemma write_bytes'_success_preserves_enc_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and fits: "\<not> cap - pos < len"
      and dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   enc_cache_abs t c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  using fits
  apply simp
  apply (rule runs_to_weaken[
    OF write_bytes_loop_preserves_enc_cache_abs
      [OF abs dst_valid src_valid]])
  by auto

lemma write_varint'_success_preserves_enc_cache_abs_bounded:
  assumes abs: "enc_cache_abs s c"
      and size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   enc_cache_abs t c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_varint'_success_preserves_cache_fields_bounded
      [OF size fits dst_valid]])
  using abs by (auto simp: enc_cache_abs_def)

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

lemma cache_update'_preserves_heap_bytes3:
  assumes near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
  shows "cache_update' addr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_bytes t out3 out3_n = heap_bytes s out3 out3_n \<rbrace>"
  unfolding cache_update'_def
  apply runs_to_vcg
  using near_ptr_lt by (auto simp: word_less_nat_alt unat_mod)

lemma cache_update'_enc_cache_abs:
  assumes abs: "enc_cache_abs s c"
  shows "cache_update' addr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               enc_cache_abs t (cache_update c (unat addr)) \<and>
               (enc_cache_wf c \<longrightarrow> enc_cache_wf (cache_update c (unat addr))) \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t buf n = heap_bytes s buf n \<rbrace>"
proof -
  have np_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  show ?thesis
    apply (rule runs_to_weaken[
      OF cache_update'_state[OF np_lt, where buf = buf and n = n]])
    using enc_cache_abs_update_state[OF abs np_lt, of addr]
          unat_lt2p[of addr]
    by (auto simp: enc_cache_abs_def intro: enc_cache_wf_update)
qed

lemma cache_update'_enc_cache_abs_wf:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
  shows "cache_update' addr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               enc_cache_abs t (cache_update c (unat addr)) \<and>
               enc_cache_wf (cache_update c (unat addr)) \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t buf n = heap_bytes s buf n \<rbrace>"
  apply (rule runs_to_weaken[OF cache_update'_enc_cache_abs[OF abs, where buf = buf and n = n]])
  using wf by auto

lemma emit_address'_success_byte_preserves_enc_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and pos_lt: "addr_pos < addr_cap"
      and ptr_ok: "ptr_valid (heap_typing s) (addr_buf +\<^sub>p uint addr_pos)"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
                   enc_cache_abs t c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_address'_def
  using mode_ge
  apply simp
  by (rule write_byte'_success_preserves_enc_cache_abs[OF abs pos_lt ptr_ok])

lemma emit_address'_success_varint_preserves_enc_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and size: "varint_size' (mode_t_C.arg_C m) s = Some n"
      and fits: "\<not> addr_cap - addr_pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s)
             (addr_buf +\<^sub>p uint (addr_pos + of_nat j))"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
                   enc_cache_abs t c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_address'_def
  using mode_lt
  apply simp
  by (rule write_varint'_success_preserves_enc_cache_abs_bounded
      [OF abs size fits dst_valid])

lemma cache_reset'_enc_cache_abs:
  shows "cache_reset' \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               enc_cache_abs t cache_init \<and>
               enc_cache_wf cache_init \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t buf n = heap_bytes s buf n \<rbrace>"
  unfolding cache_reset'_def
  supply near_reset_loop_zeros_word[where buf = buf and n = n, runs_to_vcg]
  supply same_reset_loop_zeros_word[where buf = buf and n = n, runs_to_vcg]
  apply runs_to_vcg
  subgoal premises prems for t ta
  proof -
    have np: "near_ptr_'' ta = 0"
      using prems by simp
    have near_zero: "\<forall>i < (4 :: nat). near_arr_'' ta .[i] = (0 :: 32 word)"
      using prems by simp
    have same_zero: "\<forall>i < (768 :: nat). same_arr_'' ta .[i] = (0 :: 32 word)"
      using prems by simp
    have abs: "enc_cache_abs ta cache_init"
      by (rule enc_cache_abs_cache_initI[OF np near_zero same_zero])
    have typing: "heap_typing ta = heap_typing s"
      using prems by simp
    have bytes: "heap_bytes ta buf n = heap_bytes s buf n"
      using prems by simp
    show ?thesis
      using abs typing bytes by simp
  qed
  subgoal by simp
  subgoal by simp
  done

lemma enc_cache_self_wf_encoding:
  assumes arg: "mode_t_C.arg_C m = addr"
      and mode: "mode_t_C.mode_C m = 0"
  shows "wf_encoding c (unat addr) here (unat (mode_t_C.mode_C m))
           (varint_encode (unat (mode_t_C.arg_C m)))"
  using assms by (simp add: wf_encoding_def)

lemma enc_cache_here_wf_encoding:
  assumes arg: "mode_t_C.arg_C m = here_w - addr"
      and mode: "mode_t_C.mode_C m = 1"
      and addr_le_here: "addr \<le> here_w"
  shows "wf_encoding c (unat addr) (unat here_w) (unat (mode_t_C.mode_C m))
           (varint_encode (unat (mode_t_C.arg_C m)))"
proof -
  have unat_arg: "unat (mode_t_C.arg_C m) = unat here_w - unat addr"
    using arg addr_le_here by unat_arith
  show ?thesis
    using mode addr_le_here unat_arg
    by (simp add: wf_encoding_def word_le_nat_alt)
qed

lemma enc_cache_near_wf_encoding:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and i_lt: "i < s_near"
      and mode: "mode_t_C.mode_C m = of_nat (2 + i)"
      and arg: "mode_t_C.arg_C m = addr - near_arr_'' s .[i]"
      and base_le: "near_arr_'' s .[i] \<le> addr"
  shows "wf_encoding c (unat addr) here (unat (mode_t_C.mode_C m))
           (varint_encode (unat (mode_t_C.arg_C m)))"
proof -
  have near_eq: "unat (near_arr_'' s .[i]) = near c ! i"
    using enc_cache_abs_near_unat[OF abs wf i_lt] .
  have i_lt_4: "i < 4"
    using i_lt by (simp add: s_near_def)
  have mode_unat: "unat (mode_t_C.mode_C m) = 2 + i"
    using mode i_lt_4 by (simp add: unat_word_ariths unat_of_nat_eq)
  have arg_unat:
    "unat (mode_t_C.arg_C m) = unat addr - near c ! i"
    using arg base_le near_eq by unat_arith
  have near_le: "near c ! i \<le> unat addr"
    using base_le near_eq by (simp add: word_le_nat_alt)
  show ?thesis
    using i_lt mode_unat arg_unat near_le
    by (simp add: wf_encoding_def)
qed

lemma enc_cache_same_wf_encoding:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and bank_lt: "bank < s_same"
      and mode: "mode_t_C.mode_C m = of_nat (2 + s_near + bank)"
      and arg: "mode_t_C.arg_C m = addr mod 256"
      and same_hit:
        "same_arr_'' s .[bank * 256 + unat (addr mod 256 :: 32 word)] = addr"
      and addr_ne: "addr \<noteq> 0"
  shows "wf_encoding c (unat addr) here (unat (mode_t_C.mode_C m))
           [ucast (mode_t_C.arg_C m)]"
proof -
  let ?slot = "bank * 256 + unat (addr mod 256 :: 32 word)"
  have slot_nat: "?slot = bank * 256 + unat addr mod 256"
    by (simp add: unat_mod)
  have slot_lt: "?slot < same_buckets"
    using bank_lt
    by (simp add: slot_nat same_buckets_def s_same_def)
  have same_eq: "same c ! ?slot = unat addr"
    using enc_cache_abs_same_unat[OF abs wf slot_lt] same_hit by simp
  have bank_lt_3: "bank < 3"
    using bank_lt by (simp add: s_same_def)
  have mode_unat: "unat (mode_t_C.mode_C m) = 2 + s_near + bank"
    using mode bank_lt_3 by (simp add: s_near_def unat_word_ariths unat_of_nat_eq)
  have byte_eq:
    "ucast (mode_t_C.arg_C m) = (word_of_nat (unat addr mod 256) :: byte)"
  proof -
    have lhs_unat:
      "unat (ucast (addr mod 256 :: 32 word) :: byte) = unat addr mod 256"
      by (simp add: unat_ucast unat_mod)
    have rhs_unat:
      "unat (word_of_nat (unat addr mod 256) :: byte) = unat addr mod 256"
      by (simp add: unat_of_nat_eq)
    show ?thesis
      using arg lhs_unat rhs_unat by (metis word_unat.Rep_inverse)
  qed
  have addr_unat_ne: "unat addr \<noteq> 0"
  proof
    assume unat_zero: "unat addr = 0"
    have "addr = word_of_nat (unat addr)"
      by (simp add: word_unat.Rep_inverse)
    also have "\<dots> = 0"
      using unat_zero by simp
    finally have "addr = 0" .
    then show False
      using addr_ne by simp
  qed
  show ?thesis
    using bank_lt mode_unat same_eq addr_unat_ne byte_eq slot_nat
    by (simp add: wf_encoding_def)
qed

lemma enc_cache_same_emitted_decodes:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and bank_lt: "bank < s_same"
      and same_hit:
        "same_arr_'' s .[bank * 256 + unat (addr mod 256 :: 32 word)] = addr"
      and addr_ne: "addr \<noteq> 0"
  shows "decode_address c (2 + s_near + bank) here
           ([ucast (addr mod 256 :: 32 word)] @ rest) =
         Some (unat addr, rest, cache_update c (unat addr))"
proof -
  let ?slot = "bank * 256 + unat (addr mod 256 :: 32 word)"
  have slot_nat: "?slot = bank * 256 + unat addr mod 256"
    by (simp add: unat_mod)
  have slot_lt: "?slot < same_buckets"
    using bank_lt by (simp add: slot_nat same_buckets_def s_same_def)
  have same_eq: "same c ! ?slot = unat addr"
    using enc_cache_abs_same_unat[OF abs wf slot_lt] same_hit by simp
  have mode_lt: "2 + s_near + bank < 2 + s_near + s_same"
    using bank_lt by simp
  have b_unat:
    "unat (ucast (addr mod 256 :: 32 word) :: byte) = unat addr mod 256"
    by (simp add: unat_ucast unat_mod)
  show ?thesis
    using bank_lt same_eq addr_ne mode_lt b_unat
    by (simp add: decode_address_def Let_def slot_nat)
qed

definition enc_best_wf ::
  "lifted_globals \<Rightarrow> cache \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> bool"
where
  "enc_best_wf s c addr here arg mode \<longleftrightarrow>
     (if mode < 6
      then wf_encoding c (unat addr) (unat here) (unat mode)
             (varint_encode (unat arg))
      else wf_encoding c (unat addr) (unat here) (unat mode) [ucast arg])"

definition enc_mode_arg_wf ::
  "cache \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> mode_t_C \<Rightarrow> bool"
where
  "enc_mode_arg_wf c addr here m \<longleftrightarrow>
     (if mode_t_C.mode_C m < 6
      then wf_encoding c (unat addr) (unat here) (unat (mode_t_C.mode_C m))
             (varint_encode (unat (mode_t_C.arg_C m)))
      else wf_encoding c (unat addr) (unat here) (unat (mode_t_C.mode_C m))
             [ucast (mode_t_C.arg_C m)])"

lemma enc_mode_arg_wf_mode_le8:
  assumes "enc_mode_arg_wf c addr here m"
  shows "unat (mode_t_C.mode_C m) \<le> 8"
  using assms
  unfolding enc_mode_arg_wf_def wf_encoding_def
  by (auto simp: word_less_nat_alt s_near_def s_same_def split: if_splits)

lemma enc_mode_arg_wf_mode_word_le8:
  assumes "enc_mode_arg_wf c addr here m"
  shows "mode_t_C.mode_C m \<le> (8 :: 32 word)"
  using enc_mode_arg_wf_mode_le8[OF assms]
  by (simp add: word_le_nat_alt)

lemma enc_mode_arg_wf_wf_encoding_varint_bytes32:
  assumes wf: "enc_mode_arg_wf c addr here m"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and size: "varint_size' (mode_t_C.arg_C m) s = Some n"
  shows "wf_encoding c (unat addr) (unat here)
          (unat (mode_t_C.mode_C m))
          (varint_bytes32 (mode_t_C.arg_C m) n)"
  using wf mode_lt varint_bytes32_eq_varint_encode[OF size]
  by (simp add: enc_mode_arg_wf_def)

lemma enc_mode_arg_wf_wf_encoding_byte:
  assumes wf: "enc_mode_arg_wf c addr here m"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
  shows "wf_encoding c (unat addr) (unat here)
          (unat (mode_t_C.mode_C m)) [ucast (mode_t_C.arg_C m)]"
  using wf mode_ge
  by (simp add: enc_mode_arg_wf_def)

lemma enc_best_wf_self:
  "enc_best_wf s c addr here addr 0"
  by (simp add: enc_best_wf_def wf_encoding_def)

lemma enc_best_wf_here:
  assumes addr_lt_here: "addr < here"
  shows "enc_best_wf s c addr here (here - addr) 1"
proof -
  have addr_le_here: "addr \<le> here"
    using addr_lt_here by (simp add: word_less_nat_alt word_le_nat_alt)
  have arg_unat: "unat (here - addr) = unat here - unat addr"
    using addr_le_here by unat_arith
  show ?thesis
    using addr_le_here arg_unat
    by (simp add: enc_best_wf_def wf_encoding_def word_le_nat_alt)
qed

lemma enc_best_wf_near:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and i_lt: "unat i < s_near"
      and base_le: "near_arr_'' s .[unat i] \<le> addr"
  shows "enc_best_wf s c addr here (addr - near_arr_'' s .[unat i]) (2 + i)"
proof -
  have near_eq: "unat (near_arr_'' s .[unat i]) = near c ! unat i"
    using enc_cache_abs_near_unat[OF abs wf i_lt] .
  have mode_unat: "unat (2 + i :: 32 word) = 2 + unat i"
    using i_lt by (simp add: s_near_def unat_word_ariths)
  have arg_unat:
    "unat (addr - near_arr_'' s .[unat i]) =
     unat addr - near c ! unat i"
  proof -
    have "unat (addr - near_arr_'' s .[unat i]) =
          unat addr - unat (near_arr_'' s .[unat i])"
      using base_le by (simp add: unat_sub word_le_nat_alt)
    then show ?thesis
      using near_eq by simp
  qed
  have near_le: "near c ! unat i \<le> unat addr"
    using base_le near_eq by (simp add: word_le_nat_alt)
  have wf_enc:
    "wf_encoding c (unat addr) (unat here) (unat (2 + i :: 32 word))
       (varint_encode (unat (addr - near_arr_'' s .[unat i])))"
    using i_lt mode_unat arg_unat near_le
    by (simp add: wf_encoding_def)
  have mode_lt: "(2 + i :: 32 word) < 6"
    using i_lt by (simp add: s_near_def word_less_nat_alt unat_word_ariths)
  show ?thesis
    using wf_enc mode_lt by (simp add: enc_best_wf_def)
qed

lemma enc_best_wf_same:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and bank_lt: "unat i < s_same"
      and addr_ne: "addr \<noteq> 0"
      and same_hit:
        "same_arr_'' s .[unat (i * 0x100 + addr mod 0x100)] = addr"
  shows "enc_best_wf s c addr here (addr mod 0x100) (6 + i)"
proof -
  have slot_unat:
    "unat (i * 0x100 + addr mod 0x100 :: 32 word) =
     unat i * 256 + unat (addr mod 256 :: 32 word)"
  proof -
    have i_lt_3: "unat i < 3"
      using bank_lt by (simp add: s_same_def)
    have i_mult: "unat (i * 0x100 :: 32 word) = unat i * 256"
      using i_lt_3 by (simp add: unat_word_ariths)
    have sum_lt: "unat i * 256 + unat (addr mod 256 :: 32 word) < 2 ^ 32"
      using i_lt_3 by (simp add: unat_mod)
    show ?thesis
      using i_mult sum_lt
      by (simp add: unat_word_ariths unat_mod)
  qed
  have slot_lt: "unat i * 256 + unat (addr mod 256 :: 32 word) < same_buckets"
    using bank_lt by (simp add: same_buckets_def s_same_def unat_mod)
  have same_eq: "same c ! (unat i * 256 + unat (addr mod 256 :: 32 word)) = unat addr"
    using enc_cache_abs_same_unat[OF abs wf slot_lt] same_hit slot_unat by simp
  have mode_unat: "unat (6 + i :: 32 word) = 6 + unat i"
    using bank_lt by (simp add: s_same_def unat_word_ariths)
  have addr_mod_unat:
    "unat (addr mod 0x100 :: 32 word) = unat addr mod 256"
    by (simp add: unat_mod)
  have byte_eq:
    "(ucast (addr mod 0x100 :: 32 word) :: byte) =
     word_of_nat (unat addr mod 256)"
  proof -
    have lhs_unat:
      "unat (ucast (addr mod 0x100 :: 32 word) :: byte) = unat addr mod 256"
      by (simp add: unat_ucast unat_mod)
    have rhs_unat:
      "unat (word_of_nat (unat addr mod 256) :: byte) = unat addr mod 256"
      by (simp add: unat_of_nat_eq)
    show ?thesis
      using lhs_unat rhs_unat by (simp add: word_unat_eq_iff)
  qed
  have addr_unat_ne: "unat addr \<noteq> 0"
  proof
    assume unat_zero: "unat addr = 0"
    have "addr = word_of_nat (unat addr)"
      by (simp add: word_unat.Rep_inverse)
    also have "\<dots> = 0"
      using unat_zero by simp
    finally have "addr = 0" .
    then show False using addr_ne by simp
  qed
  have wf_enc:
    "wf_encoding c (unat addr) (unat here) (unat (6 + i :: 32 word))
       [ucast (addr mod 0x100 :: 32 word)]"
    using bank_lt same_eq mode_unat byte_eq addr_unat_ne addr_mod_unat
    by (simp add: wf_encoding_def s_near_def)
  have mode_ge: "\<not> (6 + i :: 32 word) < 6"
  proof
    assume lt: "(6 + i :: 32 word) < 6"
    then have "unat (6 + i :: 32 word) < 6"
      by (simp add: word_less_nat_alt)
    then show False
      using mode_unat by simp
  qed
  show ?thesis
    using wf_enc mode_ge by (simp add: enc_best_wf_def)
qed

lemma enc_best_measure_decrease:
  fixes i :: "32 word"
  assumes i_lt: "unat i < n"
      and n_lt: "n < 2 ^ 32"
  shows "n - unat (i + 1) < n - unat i"
proof -
  have no_overflow: "unat i + unat (1 :: 32 word) < 2 ^ 32"
    using i_lt n_lt by simp
  have suc: "unat (i + 1) = Suc (unat i)"
    using no_overflow by (simp add: unat_word_ariths(1))
  show ?thesis
    using i_lt by (simp add: suc)
qed

lemma enc_best_counter_suc_le:
  fixes i :: "32 word"
  assumes i_lt: "unat i < n"
      and n_lt: "n < 2 ^ 32"
  shows "unat (i + 1) \<le> n"
proof -
  have no_overflow: "unat i + unat (1 :: 32 word) < 2 ^ 32"
    using i_lt n_lt by simp
  have suc: "unat (i + 1) = Suc (unat i)"
    using no_overflow by (simp add: unat_word_ariths(1))
  show ?thesis
    using i_lt by (simp add: suc)
qed

lemma enc_best_wf_near_bound:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and i_lt: "unat i < 4"
      and base_le: "near_arr_'' s .[unat i] \<le> addr"
  shows "enc_best_wf s c addr here (addr - near_arr_'' s .[unat i]) (2 + i)"
  apply (rule enc_best_wf_near[OF abs wf])
   using i_lt apply (simp add: s_near_def)
  using base_le apply simp
  done

lemma enc_best_same_slot_unat:
  assumes i_lt: "unat i < 3"
  shows "unat (i * 0x100 + addr mod 0x100 :: 32 word) =
         unat i * 256 + unat addr mod 256"
proof -
  have i_mult: "unat (i * 0x100 :: 32 word) = unat i * 256"
    using i_lt by (simp add: unat_word_ariths)
  have sum_lt: "unat i * 256 + unat (addr mod 0x100 :: 32 word) < 2 ^ 32"
    using i_lt by (simp add: unat_mod)
  show ?thesis
    using i_mult sum_lt
    by (simp add: unat_word_ariths unat_mod)
qed

lemma enc_best_same_slot_nat_lt:
  assumes i_lt: "unat i < 3"
  shows "unat i * 256 + unat addr mod 256 < 768"
  using i_lt by simp

lemma enc_best_same_slot_guard:
  assumes i_lt: "unat i < 3"
  shows "(i * 0x100 + addr mod 0x100 :: 32 word) < 0x300"
proof -
  have slot_lt: "unat i * 256 + unat (addr mod 0x100 :: 32 word) < 768"
    using i_lt by (simp add: unat_mod)
  show ?thesis
    using enc_best_same_slot_unat[OF i_lt, of addr] slot_lt
    by (simp add: word_less_nat_alt unat_mod)
qed

lemma enc_best_wf_same_bound:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and addr_ne: "addr \<noteq> 0"
      and bank_lt: "unat i < 3"
      and same_hit:
        "same_arr_'' s .[unat (i * 0x100 + addr mod 0x100)] = addr"
  shows "enc_best_wf s c addr here (addr mod 0x100) (6 + i)"
  apply (rule enc_best_wf_same[OF abs wf])
    using bank_lt apply (simp add: s_same_def)
   using addr_ne apply simp
  using same_hit apply simp
  done

lemma enc_best_wf_same_bound_nat_slot:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and addr_ne: "addr \<noteq> 0"
      and bank_lt: "unat i < 3"
      and same_hit:
        "same_arr_'' s .[unat i * 256 + unat addr mod 256] = addr"
  shows "enc_best_wf s c addr here (addr mod 0x100) (6 + i)"
proof -
  have same_hit_word:
    "same_arr_'' s .[unat (i * 0x100 + addr mod 0x100 :: 32 word)] = addr"
    using same_hit enc_best_same_slot_unat[OF bank_lt, of addr] by simp
  show ?thesis
    by (rule enc_best_wf_same_bound[OF abs wf addr_ne bank_lt same_hit_word])
qed

lemma enc_best_wf_same_bound_low:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and addr_ne: "addr \<noteq> 0"
      and bank_lt: "unat i < 3"
      and low_eq: "addr mod 0x100 = low"
      and same_hit:
        "same_arr_'' s .[unat (i * 0x100 + low)] = addr"
  shows "enc_best_wf s c addr here low (6 + i)"
proof -
  have same_hit_addr:
    "same_arr_'' s .[unat (i * 0x100 + addr mod 0x100)] = addr"
    using same_hit low_eq by simp
  have wf_addr:
    "enc_best_wf s c addr here (addr mod 0x100) (6 + i)"
    by (rule enc_best_wf_same_bound[OF abs wf addr_ne bank_lt same_hit_addr])
  show ?thesis
    using wf_addr low_eq by simp
qed

lemma mode_t_C_final_pair_case:
  assumes "(if p then g else Some (arg, mode)) = Some (final_arg, final_mode)"
  shows "(p \<longrightarrow>
           (case g of
              None \<Rightarrow> None
            | Some (arg, mode) \<Rightarrow> Some (mode_t_C mode arg)) =
           Some (mode_t_C final_mode final_arg)) \<and>
         (\<not> p \<longrightarrow> mode = final_mode \<and> arg = final_arg)"
  using assms by (cases p; cases g) (auto split: prod.splits)

lemma mode_t_C_final_pair_case_apply:
  assumes "(if p then g else Some (arg, mode)) = Some (final_arg, final_mode)"
  shows "(p \<longrightarrow>
           (case g of
              None \<Rightarrow> None
            | Some x \<Rightarrow>
                (case x of (arg, mode) \<Rightarrow> \<lambda>_. Some (mode_t_C mode arg)) s) =
           Some (mode_t_C final_mode final_arg)) \<and>
         (\<not> p \<longrightarrow> mode = final_mode \<and> arg = final_arg)"
  using assms by (cases p; cases g) (auto split: prod.splits)

lemma best_mode'_encode_address_correct:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and bm: "best_mode' addr here s = Some m"
  shows "enc_mode_arg_wf c addr here m"
proof -
  let ?C_near = "\<lambda>(best_arg :: 32 word, best_mode_v :: 32 word,
                     best_sz :: 32 word, i :: 32 word) s. i < 4"
  let ?B_near = "\<lambda>(best_arg :: 32 word, best_mode_v :: 32 word,
                     best_sz :: 32 word, i :: 32 word).
       do {
         base <- ogets (\<lambda>s. near_arr_'' s .[unat i]);
         (best_arg, best_mode_v, best_sz) <-
           ocondition (\<lambda>s. base \<le> addr)
            (do {
               sz <- varint_size' (addr - base);
               oreturn
                (if sz < best_sz then (addr - base, 2 + i, sz)
                 else (best_arg, best_mode_v, best_sz))
             })
            (oreturn (best_arg, best_mode_v, best_sz));
         oreturn (best_arg, best_mode_v, best_sz, i + 1)
       }"
  let ?I_near = "\<lambda>(best_arg :: 32 word, best_mode_v :: 32 word,
                     best_sz :: 32 word, i :: 32 word) st.
       enc_best_wf s c addr here best_arg best_mode_v \<and> unat i \<le> 4"
  let ?C_same = "\<lambda>(best_arg :: 32 word, best_mode_v :: 32 word,
                    best_sz :: 32 word, i :: 32 word) s. i < 3"
  let ?B_same = "\<lambda>(best_arg :: 32 word, best_mode_v :: 32 word,
                    best_sz :: 32 word, i :: 32 word).
       do {
         oguard (\<lambda>_. i * 0x100 + addr mod 0x100 < 0x300);
         ogets
          (\<lambda>s. (case if same_arr_'' s .[unat (i * 0x100 + addr mod 0x100)] =
                         addr \<and> 1 < best_sz
                     then (addr mod 0x100, 6 + i, 1)
                     else (best_arg, best_mode_v, best_sz) of
                (x1, x2, x3) \<Rightarrow> \<lambda>_. (x1, x2, x3, i + 1)) s)
       }"
	  let ?I_same = "\<lambda>(best_arg :: 32 word, best_mode_v :: 32 word,
	                    best_sz :: 32 word, i :: 32 word) st.
	       enc_best_wf s c addr here best_arg best_mode_v \<and> unat i \<le> 3"
	  let ?B_near_unfolded = "\<lambda>(best_arg :: 32 word, best_mode_v :: 32 word,
	                              best_sz :: 32 word, i :: 32 word) st.
	       (case if near_arr_'' st .[unat i] \<le> addr
	             then case varint_size' (addr - near_arr_'' st .[unat i]) st of
	                    None \<Rightarrow> None
	                  | Some sz \<Rightarrow>
	                      Some
	                       (if sz < best_sz
	                        then (addr - near_arr_'' st .[unat i], 2 + i, sz)
	                        else (best_arg, best_mode_v, best_sz))
	             else Some (best_arg, best_mode_v, best_sz) of
	          None \<Rightarrow> None
	        | Some x \<Rightarrow>
	            (case x of
	               (best_arg, best_mode_v, best_sz) \<Rightarrow>
	                 \<lambda>_. Some (best_arg, best_mode_v, best_sz, i + 1)) st)"
	  let ?B_same_unfolded = "\<lambda>(best_arg :: 32 word, best_mode_v :: 32 word,
	                              best_sz :: 32 word, i :: 32 word) st.
	       (case if i * 0x100 + addr mod 0x100 < 0x300 then Some () else None of
	          None \<Rightarrow> None
	        | Some _ \<Rightarrow>
	            Some
	             (fst (if same_arr_'' st .[unat (i * 0x100 + addr mod 0x100)] =
	                       addr \<and> 1 < best_sz
	                    then (addr mod 0x100, 6 + i, 1)
	                    else (best_arg, best_mode_v, best_sz)),
	              fst (snd (if same_arr_'' st .[unat (i * 0x100 + addr mod 0x100)] =
	                            addr \<and> 1 < best_sz
	                         then (addr mod 0x100, 6 + i, 1)
	                         else (best_arg, best_mode_v, best_sz))),
	              snd (snd (if same_arr_'' st .[unat (i * 0x100 + addr mod 0x100)] =
	                            addr \<and> 1 < best_sz
	                         then (addr mod 0x100, 6 + i, 1)
	                         else (best_arg, best_mode_v, best_sz))),
	              i + 1))"
	  have B_near_unfolded_eq: "?B_near = ?B_near_unfolded"
	    by (auto simp: fun_eq_iff obind_def ocondition_def ogets_def K_def
	        split: prod.splits option.splits)
	  have B_same_unfolded_eq: "?B_same = ?B_same_unfolded"
	    by (auto simp: fun_eq_iff obind_def oguard_def ogets_def K_def
	        split: prod.splits option.splits)

	  have near_loop:
    "case owhile ?C_near ?B_near init s of
       None \<Rightarrow> False
     | Some r \<Rightarrow> ?I_near r s"
    if init_wf: "?I_near init s"
    for init
  proof -
    show ?thesis
      apply (rule Reader_Monad.owhile_rule
        [where I = ?I_near
           and M = "measure (\<lambda>x. case x of
             (best_arg :: 32 word, best_mode_v :: 32 word,
              best_sz :: 32 word, i :: 32 word) \<Rightarrow> 4 - unat i)"])
      using init_wf abs wf
      apply (simp_all add: Reader_Monad.oreturn_apply ogets_def
          ocondition_def word_less_nat_alt)
      subgoal
        by (auto simp: Reader_Monad.oreturn_apply enc_best_measure_decrease
            split: prod.splits)
      subgoal
        apply (auto simp: Reader_Monad.oreturn_apply obind_def ogets_def
            ocondition_def varint_size'_some word_less_nat_alt s_near_def
            split: prod.splits if_splits option.splits)
        subgoal
          by (rule enc_best_wf_near_bound[OF abs wf]) simp_all
        subgoal
          by (rule enc_best_counter_suc_le) simp_all
        subgoal
          by (rule enc_best_counter_suc_le) simp_all
        subgoal
          by (rule enc_best_counter_suc_le) simp_all
        done
      subgoal
        by (auto simp: Reader_Monad.oreturn_apply obind_def ogets_def
            ocondition_def varint_size'_neq_None
            split: prod.splits if_splits option.splits)
      done
  qed

  have same_loop:
    "case owhile ?C_same ?B_same init s of
       None \<Rightarrow> False
     | Some r \<Rightarrow> ?I_same r s"
    if init_wf: "?I_same init s"
      and addr_ne: "addr \<noteq> 0"
    for init
  proof -
    show ?thesis
      apply (rule Reader_Monad.owhile_rule
        [where I = ?I_same
           and M = "measure (\<lambda>x. case x of
             (best_arg :: 32 word, best_mode_v :: 32 word,
              best_sz :: 32 word, i :: 32 word) \<Rightarrow> 3 - unat i)"])
      using init_wf abs wf addr_ne
      apply (simp_all add: Reader_Monad.oreturn_apply ogets_def oguard_def
          word_less_nat_alt)
      subgoal
        by (auto simp: Reader_Monad.oreturn_apply enc_best_measure_decrease
            split: prod.splits)
      subgoal
        apply (auto simp: Reader_Monad.oreturn_apply word_less_nat_alt s_same_def
            split: prod.splits if_splits option.splits)
        subgoal
          by (rule enc_best_wf_same_bound_low[OF abs wf]) simp_all
        subgoal
          by (rule enc_best_counter_suc_le) simp_all
        subgoal
          by (rule enc_best_counter_suc_le) simp_all
        subgoal
          by (rule enc_best_counter_suc_le) simp_all
        done
      subgoal
        by (auto simp: obind_def oguard_def ogets_def word_less_nat_alt unat_word_ariths
            enc_best_same_slot_nat_lt
            intro: enc_best_same_slot_guard
            split: prod.splits)
      done
  qed

  obtain best_sz where sz0: "varint_size' addr s = Some best_sz"
    using varint_size'_some by blast
  let ?best0 = "(addr, 0 :: 32 word, best_sz)"
  have best0_wf: "enc_best_wf s c addr here addr 0"
    by (rule enc_best_wf_self)
  have best1_case:
    "case (if addr < here
           then case varint_size' (here - addr) s of
                  None \<Rightarrow> None
                | Some sz \<Rightarrow>
                    Some (if sz < best_sz then (here - addr, 1, sz) else ?best0)
           else Some ?best0) of
       None \<Rightarrow> False
     | Some (best_arg, best_mode_v, best_sz) \<Rightarrow>
         enc_best_wf s c addr here best_arg best_mode_v"
    using best0_wf enc_best_wf_here[of addr here s c]
    by (auto simp: varint_size'_neq_None split: option.splits)

  let ?best1 =
    "(if addr < here
      then case varint_size' (here - addr) s of
             None \<Rightarrow> None
           | Some sz \<Rightarrow>
               Some (if sz < best_sz then (here - addr, 1, sz) else ?best0)
      else Some ?best0)"
  obtain best_arg1 best_mode1 best_sz1 where best1:
      "?best1 = Some (best_arg1, best_mode1, best_sz1)"
    and wf1: "enc_best_wf s c addr here best_arg1 best_mode1"
    using best1_case by (cases ?best1) auto

  have near_init: "?I_near (best_arg1, best_mode1, best_sz1, 0) s"
    using wf1 by simp
	  obtain best_arg2 best_mode2 best_sz2 i2 where near_res:
	      "owhile ?C_near ?B_near (best_arg1, best_mode1, best_sz1, 0) s =
	       Some (best_arg2, best_mode2, best_sz2, i2)"
	    and wf2: "enc_best_wf s c addr here best_arg2 best_mode2"
	    using near_loop[OF near_init]
	    by (cases "owhile ?C_near ?B_near (best_arg1, best_mode1, best_sz1, 0) s")
	       (auto split: prod.splits)
	  have near_res_unfolded:
	      "owhile ?C_near ?B_near_unfolded (best_arg1, best_mode1, best_sz1, 0) s =
	       Some (best_arg2, best_mode2, best_sz2, i2)"
	    using near_res[unfolded B_near_unfolded_eq] .

	  have final_pair:
    "\<exists>final_arg final_mode.
       (if addr \<noteq> 0
        then case owhile ?C_same ?B_same (best_arg2, best_mode2, best_sz2, 0) s of
               None \<Rightarrow> None
             | Some (best_arg, best_mode_v, best_sz, i) \<Rightarrow>
                 Some (best_arg, best_mode_v)
        else Some (best_arg2, best_mode2)) =
       Some (final_arg, final_mode) \<and>
       enc_best_wf s c addr here final_arg final_mode"
  proof (cases "addr = 0")
    case True
    then show ?thesis
      using wf2 by auto
  next
    case False
    have same_init: "?I_same (best_arg2, best_mode2, best_sz2, 0) s"
      using wf2 by simp
    obtain final_arg final_mode final_sz final_i where same_res:
        "owhile ?C_same ?B_same (best_arg2, best_mode2, best_sz2, 0) s =
         Some (final_arg, final_mode, final_sz, final_i)"
      and wf_final: "enc_best_wf s c addr here final_arg final_mode"
      using same_loop[OF same_init False]
      by (cases "owhile ?C_same ?B_same (best_arg2, best_mode2, best_sz2, 0) s")
         (auto split: prod.splits)
    show ?thesis
      using False same_res wf_final by auto
  qed
	  then obtain final_arg final_mode where final_pair_res:
	      "(if addr \<noteq> 0
	        then case owhile ?C_same ?B_same (best_arg2, best_mode2, best_sz2, 0) s of
	               None \<Rightarrow> None
             | Some (best_arg, best_mode_v, best_sz, i) \<Rightarrow>
                 Some (best_arg, best_mode_v)
        else Some (best_arg2, best_mode2)) =
       Some (final_arg, final_mode)"
	    and wf_final: "enc_best_wf s c addr here final_arg final_mode"
	    by blast
	  have final_pair_res_unfolded:
	      "(if addr \<noteq> 0
	        then case owhile ?C_same ?B_same_unfolded
	                    (best_arg2, best_mode2, best_sz2, 0) s of
	               None \<Rightarrow> None
	             | Some x \<Rightarrow>
	                 (case x of
	                    (best_arg, best_mode_v, best_sz, i) \<Rightarrow>
	                      \<lambda>_. Some (best_arg, best_mode_v)) s
	        else Some (best_arg2, best_mode2)) =
	       Some (final_arg, final_mode)"
	  proof (cases "addr = 0")
	    case True
	    then show ?thesis
	      using final_pair_res[unfolded B_same_unfolded_eq] by simp
	  next
	    case False
	    then show ?thesis
	      using final_pair_res[unfolded B_same_unfolded_eq]
	      by (cases "owhile ?C_same ?B_same_unfolded
	            (best_arg2, best_mode2, best_sz2, 0) s")
	         (auto split: prod.splits)
		  qed
	  let ?final_mode_res =
	    "(if addr \<noteq> 0
	      then case (case owhile ?C_same ?B_same_unfolded
	                     (best_arg2, best_mode2, best_sz2, 0) s of
	                None \<Rightarrow> None
	              | Some x \<Rightarrow>
	                  (case x of
	                     (best_arg, best_mode_v, best_sz, i) \<Rightarrow>
	                       \<lambda>_. Some (best_arg, best_mode_v)) s) of
	             None \<Rightarrow> None
	           | Some x \<Rightarrow>
	               (case x of
	                  (best_arg, best_mode_v) \<Rightarrow>
	                    \<lambda>_. Some (mode_t_C best_mode_v best_arg)) s
	      else Some (mode_t_C best_mode2 best_arg2))"
	  have final_ctor: "?final_mode_res = Some (mode_t_C final_mode final_arg)"
	  proof (cases "addr = 0")
	    case True
	    then show ?thesis
	      using final_pair_res_unfolded by simp
	  next
	    case False
	    then show ?thesis
	      using final_pair_res_unfolded
	      by simp
	  qed

		  have bm_final: "best_mode' addr here s = Some (mode_t_C final_mode final_arg)"
	  proof (cases "addr < here")
	    case True
	    note here_lt = True
    have first_eval:
      "(case varint_size' (here - addr) s of
          None \<Rightarrow> None
        | Some sz \<Rightarrow>
            Some
             (if sz < best_sz then (here - addr, 1, sz)
              else (addr, 0, best_sz))) =
       Some (best_arg1, best_mode1, best_sz1)"
      using best1 True
      by (cases "varint_size' (here - addr) s")
         (simp_all add: enc_oreturn_apply)
	    have eval: "best_mode' addr here s = ?final_mode_res"
	      using sz0 here_lt first_eval near_res_unfolded
	      unfolding best_mode'_def
	      by (simp add: obind_def ocondition_def ogets_def oguard_def K_def
	          Reader_Monad.oreturn_apply Reader_Monad.oreturn_def enc_oreturn_apply
	          split_beta case_prod_beta)
	    show ?thesis
	      using eval final_ctor by simp
	  next
	    case False
	    note here_ge = False
    have first_eval:
      "Some (addr, 0, best_sz) = Some (best_arg1, best_mode1, best_sz1)"
      using best1 False by (simp add: enc_oreturn_apply)
	    have first_eqs:
	      "best_arg1 = addr" "best_mode1 = 0" "best_sz1 = best_sz"
	      using first_eval by simp_all
	    have near_res_addr:
	      "owhile ?C_near ?B_near_unfolded (addr, 0, best_sz, 0) s =
	       Some (best_arg2, best_mode2, best_sz2, i2)"
	      using near_res_unfolded first_eqs by simp
	    have eval: "best_mode' addr here s = ?final_mode_res"
	      using sz0 here_ge near_res_addr
	      unfolding best_mode'_def
	      by (simp add: obind_def ocondition_def ogets_def oguard_def K_def
	          Reader_Monad.oreturn_apply Reader_Monad.oreturn_def enc_oreturn_apply
	          split_beta case_prod_beta)
	    show ?thesis
	      using eval final_ctor by simp
  qed
  have m_eq: "m = mode_t_C final_mode final_arg"
    using bm bm_final by simp
  show ?thesis
    using wf_final m_eq
    by (simp add: enc_mode_arg_wf_def enc_best_wf_def)
qed

end

end
