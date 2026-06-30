theory VcdiffEnc_Serialize
  imports
    VcdiffEnc_Emit
    VcdiffEnc_Match
begin

context vcdiff_enc_global_addresses begin

lemma varint_size'_less_128:
  fixes v :: "32 word"
  assumes v_lt: "v < 128"
  shows "varint_size' v s = Some 1"
proof -
  have shift0_unat: "unat (v >> (7 :: nat)) = 0"
    using v_lt
    by (simp add: Word_Lemmas.shiftr_div_2n' word_less_nat_alt)
  have shift0: "v >> (7 :: nat) = 0"
    using shift0_unat by (metis word_unat.Rep_inject unat_0)
  show ?thesis
    unfolding varint_size'_def
    by (simp add: shift0 Reader_Monad.owhile_def
                  Reader_Monad.obind_def Reader_Monad.oreturn_def
                  Reader_Monad.option_while_simps K_def)
qed

lemma varint_size'_0[simp]:
  "varint_size' 0 s = Some 1"
  by (rule varint_size'_less_128) simp

lemma varint_size'_5[simp]:
  "varint_size' 5 s = Some 1"
  by (rule varint_size'_less_128) simp

lemma varint_bytes32_0_1[simp]:
  "varint_bytes32 0 1 = [0]"
  by (simp add: varint_bytes32_def varint_byte32_def)

lemma varint_bytes32_5_1[simp]:
  "varint_bytes32 5 1 = [5]"
  by (simp add: varint_bytes32_def varint_byte32_def)

lemma varint_encode_0[simp]:
  "varint_encode 0 = [0]"
  by (simp add: varint_encode_def)

lemma varint_size_pos[simp]:
  "0 < varint_size n"
  using varint_encode_length varint_encode_nonempty
  by (metis length_greater_0_conv)

lemma one_le_varint_size_plus[simp]:
  "Suc 0 \<le> varint_size n + m"
  using varint_size_pos[of n] by linarith

lemma heap_bytes_0[simp]:
  "heap_bytes s buf 0 = []"
  by (simp add: heap_bytes_def)

lemma bufs_disjoint_word_range_rightD:
  fixes pos len :: "32 word"
  assumes disj: "bufs_disjoint p pn q qn"
      and k_lt: "k < pn"
      and i_lt: "i < unat len"
      and no_overflow: "unat pos + unat len < 2 ^ 32"
      and range: "unat pos + unat len \<le> qn"
  shows "p +\<^sub>p int k \<noteq> q +\<^sub>p uint (pos + of_nat i :: 32 word)"
proof -
  have idx: "unat (pos + of_nat i :: 32 word) = unat pos + i"
    by (rule unat_add_of_nat_index[OF i_lt no_overflow])
  have pos_i_lt: "unat pos + i < qn"
    using i_lt range by simp
  have neq: "p +\<^sub>p int k \<noteq> q +\<^sub>p int (unat pos + i)"
    using disj k_lt pos_i_lt unfolding bufs_disjoint_def by blast
  show ?thesis
  proof
    assume eq: "p +\<^sub>p int k = q +\<^sub>p uint (pos + of_nat i :: 32 word)"
    have "p +\<^sub>p int k = q +\<^sub>p int (unat pos + i)"
      using eq idx by (simp only: uint_nat)
    thus False using neq by simp
  qed
qed

lemma bufs_disjoint_word_range_leftD:
  fixes pos len :: "32 word"
  assumes disj: "bufs_disjoint p pn q qn"
      and i_lt: "i < unat len"
      and no_overflow: "unat pos + unat len < 2 ^ 32"
      and range: "unat pos + unat len \<le> pn"
      and k_lt: "k < qn"
  shows "p +\<^sub>p uint (pos + of_nat i :: 32 word) \<noteq> q +\<^sub>p int k"
proof -
  have idx: "unat (pos + of_nat i :: 32 word) = unat pos + i"
    by (rule unat_add_of_nat_index[OF i_lt no_overflow])
  have pos_i_lt: "unat pos + i < pn"
    using i_lt range by simp
  have neq: "p +\<^sub>p int (unat pos + i) \<noteq> q +\<^sub>p int k"
    using disj pos_i_lt k_lt unfolding bufs_disjoint_def by blast
  show ?thesis
  proof
    assume eq: "p +\<^sub>p uint (pos + of_nat i :: 32 word) = q +\<^sub>p int k"
    have "p +\<^sub>p int (unat pos + i) = q +\<^sub>p int k"
      using eq idx by (simp only: uint_nat)
    thus False using neq by simp
  qed
qed

lemma bufs_disjoint_word_rangesD:
  fixes p_pos p_len q_pos q_len :: "32 word"
  assumes disj: "bufs_disjoint p pn q qn"
      and i_lt: "i < unat p_len"
      and j_lt: "j < unat q_len"
      and p_no_overflow: "unat p_pos + unat p_len < 2 ^ 32"
      and q_no_overflow: "unat q_pos + unat q_len < 2 ^ 32"
      and p_range: "unat p_pos + unat p_len \<le> pn"
      and q_range: "unat q_pos + unat q_len \<le> qn"
  shows "p +\<^sub>p uint (p_pos + of_nat i :: 32 word) \<noteq>
         q +\<^sub>p uint (q_pos + of_nat j :: 32 word)"
proof -
  have p_idx: "unat (p_pos + of_nat i :: 32 word) = unat p_pos + i"
    by (rule unat_add_of_nat_index[OF i_lt p_no_overflow])
  have q_idx: "unat (q_pos + of_nat j :: 32 word) = unat q_pos + j"
    by (rule unat_add_of_nat_index[OF j_lt q_no_overflow])
  have p_i_lt: "unat p_pos + i < pn"
    using i_lt p_range by simp
  have q_j_lt: "unat q_pos + j < qn"
    using j_lt q_range by simp
  have neq:
    "p +\<^sub>p int (unat p_pos + i) \<noteq>
     q +\<^sub>p int (unat q_pos + j)"
    using disj p_i_lt q_j_lt unfolding bufs_disjoint_def by blast
  show ?thesis
  proof
    assume eq:
      "p +\<^sub>p uint (p_pos + of_nat i :: 32 word) =
       q +\<^sub>p uint (q_pos + of_nat j :: 32 word)"
    have "p +\<^sub>p int (unat p_pos + i) =
          q +\<^sub>p int (unat q_pos + j)"
      using eq p_idx q_idx by (simp only: uint_nat)
    thus False using neq by simp
  qed
qed

lemma bufs_disjoint_word_point_rightD:
  assumes disj: "bufs_disjoint p pn q qn"
      and k_lt: "k < pn"
      and pos_lt: "unat pos < qn"
  shows "p +\<^sub>p int k \<noteq> q +\<^sub>p uint pos"
proof -
  have neq: "p +\<^sub>p int k \<noteq> q +\<^sub>p int (unat pos)"
    using disj k_lt pos_lt unfolding bufs_disjoint_def by blast
  show ?thesis
  proof
    assume eq: "p +\<^sub>p int k = q +\<^sub>p uint pos"
    have "p +\<^sub>p int k = q +\<^sub>p int (unat pos)"
      using eq by (simp only: uint_nat)
    thus False using neq by simp
  qed
qed

lemma write_byte'_heap_bytes_append_next_typing_preserves3:
  assumes pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and dist: "ptr_range_distinct buf (Suc (unat pos))"
      and disj1: "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
      and disj2: "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
      and disj3: "\<forall>i < out3_n. out3 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + 1)) =
                   heap_bytes s buf (unat pos) @ [b] \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   heap_bytes t out3 out3_n = heap_bytes s out3 out3_n \<and>
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
               heap_bytes t out3 out3_n = heap_bytes s out3 out3_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_success_preserves_heap_bytes
      [OF pos_lt ptr_ok disj3])
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
           heap_bytes t out3 out3_n = heap_bytes s out3 out3_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append2 pres3 by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma write_varint'_success_heap_bytes_append_wordpos_preserves3:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
      and prefix_disj: "\<forall>k < unat pos. \<forall>i.
           i < n \<longrightarrow> buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and no_overflow: "unat pos + unat n < 2 ^ 32"
      and disj1: "\<forall>k < out1_n. \<forall>i.
           i < n \<longrightarrow> out1 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and disj2: "\<forall>k < out2_n. \<forall>i.
           i < n \<longrightarrow> out2 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and disj3: "\<forall>k < out3_n. \<forall>i.
           i < n \<longrightarrow> out3 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + n)) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   heap_bytes t out3 out3_n = heap_bytes s out3 out3_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append2:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes t buf (unat (pos + n)) =
               heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_heap_bytes_append_wordpos_preserves2
      [OF size fits dst_valid dst_inj prefix_disj no_overflow disj1 disj2])
  have pres3:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes t out3 out3_n = heap_bytes s out3 out3_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes_bounded
      [OF size fits dst_valid disj3])
  have combined:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes t buf (unat (pos + n)) =
           heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes t out3 out3_n = heap_bytes s out3 out3_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append2 pres3 by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma write_bytes'_success_heap_bytes_append_src0_wordpos_preserves2:
  assumes fits: "\<not> cap - pos < len"
      and dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
      and dst_src_disj: "\<forall>i < unat len. \<forall>j < unat len.
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           src +\<^sub>p uint ((0 :: 32 word) + of_nat j)"
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
  shows "write_bytes' buf cap pos src (0 :: 32 word) len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + len)) =
                   heap_bytes s buf (unat pos) @
                   heap_bytes s src (unat len) \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_bytes'_success_heap_bytes_append_wordpos_preserves2
      [OF fits dst_valid src_valid dst_src_disj dst_inj
          prefix_disj no_overflow disj1 disj2]])
  by (simp add: heap_bytes_word_zero)

definition serialize_byte_step_ok ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> nat \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow>
   8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "serialize_byte_step_ok s out out_cap pos data data_n inst inst_n addr addr_n \<longleftrightarrow>
     pos < out_cap \<and>
     ptr_valid (heap_typing s) (out +\<^sub>p uint pos) \<and>
     ptr_range_distinct out (Suc (unat pos)) \<and>
     (\<forall>i < data_n. data +\<^sub>p int i \<noteq> out +\<^sub>p uint pos) \<and>
     (\<forall>i < inst_n. inst +\<^sub>p int i \<noteq> out +\<^sub>p uint pos) \<and>
     (\<forall>i < addr_n. addr +\<^sub>p int i \<noteq> out +\<^sub>p uint pos)"

definition serialize_varint_step_ok ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> nat \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow>
   8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "serialize_varint_step_ok s out out_cap pos v n data data_n inst inst_n addr addr_n \<longleftrightarrow>
     varint_size' v s = Some n \<and>
     \<not> out_cap - pos < n \<and>
     (\<forall>j < unat n.
        ptr_valid (heap_typing s) (out +\<^sub>p uint (pos + of_nat j))) \<and>
     (\<forall>i < unat n. \<forall>j < unat n.
        i \<noteq> j \<longrightarrow>
        out +\<^sub>p uint (pos + of_nat i) \<noteq>
        out +\<^sub>p uint (pos + of_nat j)) \<and>
     (\<forall>k < unat pos. \<forall>i.
        i < n \<longrightarrow> out +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)) \<and>
     unat pos + unat n < 2 ^ 32 \<and>
     (\<forall>k < data_n. \<forall>i.
        i < n \<longrightarrow> data +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)) \<and>
     (\<forall>k < inst_n. \<forall>i.
        i < n \<longrightarrow> inst +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)) \<and>
     (\<forall>k < addr_n. \<forall>i.
        i < n \<longrightarrow> addr +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i))"

definition serialize_copy_step_ok ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> nat \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "serialize_copy_step_ok s out out_cap pos src len keep1 keep1_n keep2 keep2_n \<longleftrightarrow>
     \<not> out_cap - pos < len \<and>
     (\<forall>j < unat len.
        ptr_valid (heap_typing s) (out +\<^sub>p uint (pos + of_nat j))) \<and>
     (\<forall>j < unat len.
        ptr_valid (heap_typing s) (src +\<^sub>p uint ((0 :: 32 word) + of_nat j))) \<and>
     (\<forall>i < unat len. \<forall>j < unat len.
        out +\<^sub>p uint (pos + of_nat i) \<noteq>
        src +\<^sub>p uint ((0 :: 32 word) + of_nat j)) \<and>
     (\<forall>i < unat len. \<forall>j < unat len.
        i \<noteq> j \<longrightarrow>
        out +\<^sub>p uint (pos + of_nat i) \<noteq>
        out +\<^sub>p uint (pos + of_nat j)) \<and>
     (\<forall>k < unat pos. \<forall>i.
        i < len \<longrightarrow> out +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)) \<and>
     unat pos + unat len < 2 ^ 32 \<and>
     (\<forall>k < keep1_n. \<forall>i.
        i < len \<longrightarrow> keep1 +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)) \<and>
     (\<forall>k < keep2_n. \<forall>i.
        i < len \<longrightarrow> keep2 +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i))"

lemma serialize_fixed_header_byte_step:
  assumes ok:
    "serialize_byte_step_ok s out out_cap pos data data_n inst inst_n addr addr_n"
      and typing: "heap_typing st = heap_typing s"
  shows "write_byte' out out_cap pos b \<bullet> st
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t out (unat (pos + 1)) =
                   heap_bytes st out (unat pos) @ [b] \<and>
                   heap_bytes t data data_n = heap_bytes st data data_n \<and>
                   heap_bytes t inst inst_n = heap_bytes st inst inst_n \<and>
                   heap_bytes t addr addr_n = heap_bytes st addr addr_n \<and>
                   heap_typing t = heap_typing st \<rbrace>"
  using ok typing
  unfolding serialize_byte_step_ok_def
  by (intro write_byte'_heap_bytes_append_next_typing_preserves3) auto

lemma serialize_source_descriptor_varint_step:
  assumes ok:
    "serialize_varint_step_ok s out out_cap pos v n data data_n inst inst_n addr addr_n"
      and typing: "heap_typing st = heap_typing s"
  shows "write_varint' out out_cap pos v \<bullet> st
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t out (unat (pos + n)) =
                   heap_bytes st out (unat pos) @ varint_bytes32 v n \<and>
                   heap_bytes t data data_n = heap_bytes st data data_n \<and>
                   heap_bytes t inst inst_n = heap_bytes st inst inst_n \<and>
                   heap_bytes t addr addr_n = heap_bytes st addr addr_n \<and>
                   heap_typing t = heap_typing st \<rbrace>"
proof -
  have size_st: "varint_size' v st = Some n"
    using ok varint_size'_state_independent[of v st s]
    by (simp add: serialize_varint_step_ok_def)
  show ?thesis
    using ok typing size_st
    unfolding serialize_varint_step_ok_def
    by (intro write_varint'_success_heap_bytes_append_wordpos_preserves3) auto
qed

lemma serialize_delta_header_varint_step:
  assumes ok:
    "serialize_varint_step_ok s out out_cap pos v n data data_n inst inst_n addr addr_n"
      and typing: "heap_typing st = heap_typing s"
  shows "write_varint' out out_cap pos v \<bullet> st
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t out (unat (pos + n)) =
                   heap_bytes st out (unat pos) @ varint_bytes32 v n \<and>
                   heap_bytes t data data_n = heap_bytes st data data_n \<and>
                   heap_bytes t inst inst_n = heap_bytes st inst inst_n \<and>
                   heap_bytes t addr addr_n = heap_bytes st addr addr_n \<and>
                   heap_typing t = heap_typing st \<rbrace>"
  by (rule serialize_source_descriptor_varint_step[OF ok typing])

lemma serialize_section_copy_step:
  assumes ok:
    "serialize_copy_step_ok s out out_cap pos src len keep1 keep1_n keep2 keep2_n"
      and typing: "heap_typing st = heap_typing s"
  shows "write_bytes' out out_cap pos src (0 :: 32 word) len \<bullet> st
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t out (unat (pos + len)) =
                   heap_bytes st out (unat pos) @ heap_bytes st src (unat len) \<and>
                   heap_bytes t keep1 keep1_n = heap_bytes st keep1 keep1_n \<and>
                   heap_bytes t keep2 keep2_n = heap_bytes st keep2 keep2_n \<and>
                   heap_typing t = heap_typing st \<rbrace>"
  using ok typing
  unfolding serialize_copy_step_ok_def
  by (intro write_bytes'_success_heap_bytes_append_src0_wordpos_preserves2) auto

lemma serialize_empty:
  "serialize [] [] [] [] [] =
   [0xD6, 0xC3, 0xC4, 0, 0, 0, 5, 0, 0, 0, 0, 0]"
  by (simp add: serialize_def magic_bytes_def varint_encode_def
                varint_size_def to_base128_nonzero)

lemma serialize'_empty_writes_serialize:
  assumes cap: "(12 :: 32 word) \<le> out_cap"
      and out_valid: "buf_valid s out 12"
      and out_dist: "ptr_range_distinct out 12"
  shows "serialize' out out_cap 0 0 data 0 inst 0 addr 0 \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (12 :: 32 word) \<and>
                   heap_bytes t out 12 = serialize [] [] [] [] [] \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding serialize'_def
  apply runs_to_vcg
        apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
          apply (use cap in unat_arith)
         apply (insert buf_validD[OF out_valid, of 0])
         apply simp
        apply (rule ptr_range_distinct_mono[OF out_dist])
        apply simp
       apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
         apply (use cap in unat_arith)
        apply (insert buf_validD[OF out_valid, of 1])
        apply simp
       apply (rule ptr_range_distinct_mono[OF out_dist])
       apply simp
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
        apply (use cap in unat_arith)
       apply (insert buf_validD[OF out_valid, of 2])
       apply simp
      apply (rule ptr_range_distinct_mono[OF out_dist])
      apply simp
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
       apply (use cap in unat_arith)
      apply (insert buf_validD[OF out_valid, of 3])
      apply simp
     apply (rule ptr_range_distinct_mono[OF out_dist])
     apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
      apply (use cap in unat_arith)
     apply (insert buf_validD[OF out_valid, of 4])
     apply simp
    apply (rule ptr_range_distinct_mono[OF out_dist])
    apply simp
   apply clarsimp
   apply runs_to_vcg
   apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
     apply (use cap in unat_arith)
    apply (insert buf_validD[OF out_valid, of 5])
    apply simp
   apply (rule ptr_range_distinct_mono[OF out_dist])
   apply simp
  apply clarsimp
  apply runs_to_vcg
        apply (rule runs_to_weaken[
          OF write_varint'_success_heap_bytes_append_wordpos])
             apply simp
           apply (use cap in unat_arith)
           apply (intro allI impI)
           apply (insert buf_validD[OF out_valid, of 6])
           apply simp
         apply auto[1]
         apply (intro allI impI)
         apply (rule ptr_range_distinct_word_prefix_disj
           [where pos = 6 and len = 1 and total = 12, OF out_dist])
             apply simp
            apply simp
           apply assumption
          apply assumption
        apply simp
       apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[
         OF write_varint'_success_heap_bytes_append_wordpos])
            apply simp
          apply (use cap in unat_arith)
          apply (intro allI impI)
          apply (insert buf_validD[OF out_valid, of 7])
          apply simp
        apply auto[1]
        apply (intro allI impI)
        apply (rule ptr_range_distinct_word_prefix_disj
          [where pos = 7 and len = 1 and total = 12, OF out_dist])
            apply simp
           apply simp
          apply assumption
         apply assumption
       apply simp
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
        apply (use cap in unat_arith)
       apply (insert buf_validD[OF out_valid, of 8])
       apply simp
      apply (rule ptr_range_distinct_mono[OF out_dist])
      apply simp
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF write_varint'_success_heap_bytes_append_wordpos])
          apply simp
        apply (use cap in unat_arith)
        apply (intro allI impI)
        apply (insert buf_validD[OF out_valid, of 9])
        apply simp
      apply auto[1]
      apply (intro allI impI)
      apply (rule ptr_range_distinct_word_prefix_disj
        [where pos = 9 and len = 1 and total = 12, OF out_dist])
          apply simp
         apply simp
        apply assumption
       apply assumption
     apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_varint'_success_heap_bytes_append_wordpos])
         apply simp
       apply (use cap in unat_arith)
       apply (intro allI impI)
       apply (insert buf_validD[OF out_valid, of 10])
       apply simp
     apply auto[1]
     apply (intro allI impI)
     apply (rule ptr_range_distinct_word_prefix_disj
       [where pos = 10 and len = 1 and total = 12, OF out_dist])
         apply simp
        apply simp
       apply assumption
      apply assumption
    apply simp
   apply clarsimp
   apply runs_to_vcg
   apply (rule runs_to_weaken[
     OF write_varint'_success_heap_bytes_append_wordpos])
        apply simp
      apply (use cap in unat_arith)
      apply (intro allI impI)
      apply (insert buf_validD[OF out_valid, of 11])
      apply simp
    apply auto[1]
    apply (intro allI impI)
    apply (rule ptr_range_distinct_word_prefix_disj
      [where pos = 11 and len = 1 and total = 12, OF out_dist])
        apply simp
       apply simp
      apply assumption
     apply assumption
   apply simp
  apply clarsimp
  apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_bytes'_zero])
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_bytes'_zero])
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_bytes'_zero])
    apply (clarsimp simp: serialize_empty heap_bytes_def)
  done

lemma serialize'_zero_lengths_writes_serialize:
  assumes cap: "(12 :: 32 word) \<le> out_cap"
      and out_valid: "buf_valid s out 12"
      and out_dist: "ptr_range_distinct out 12"
      and src_empty: "src = []"
      and tgt_empty: "tgt = []"
      and data_empty: "data_bytes = []"
      and inst_empty: "inst_bytes = []"
      and addr_empty: "addr_bytes = []"
  shows "serialize' out out_cap 0 0 data 0 inst 0 addr 0 \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (12 :: 32 word) \<and>
                   heap_bytes t out 12 =
                     serialize src tgt data_bytes inst_bytes addr_bytes \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF serialize'_empty_writes_serialize[OF cap out_valid out_dist]])
  using src_empty tgt_empty data_empty inst_empty addr_empty by simp

lemma serialize'_no_source_writes_serialize:
  fixes src_len tgt_len data_len inst_len addr_len :: "32 word"
    and tgt_n data_n inst_n addr_n dlen_n :: "32 word"
    and src tgt data_bytes inst_bytes addr_bytes :: "byte list"
  defines "dlen_nat \<equiv>
     varint_size (length tgt) + 1 +
     varint_size (length data_bytes) +
     varint_size (length inst_bytes) +
     varint_size (length addr_bytes) +
     length data_bytes + length inst_bytes + length addr_bytes"
  defines "dlen \<equiv>
     tgt_n + 1 + data_n + inst_n + addr_n +
     data_len + inst_len + addr_len"
  defines "p_tgt \<equiv> (6 :: 32 word) + dlen_n"
  defines "p_delta \<equiv> p_tgt + tgt_n"
  defines "p_data_len \<equiv> (7 :: 32 word) + (dlen_n + tgt_n)"
  defines "p_inst_len \<equiv> p_data_len + data_n"
  defines "p_addr_len \<equiv> p_inst_len + inst_n"
  defines "p_data \<equiv> p_addr_len + addr_n"
  defines "p_inst \<equiv> p_data + data_len"
  defines "p_addr \<equiv> p_inst + inst_len"
  defines "p_end \<equiv> p_addr + addr_len"
  assumes src_len0: "src_len = 0"
      and src_empty: "src = []"
      and tgt_len: "unat tgt_len = length tgt"
      and data_len: "unat data_len = length data_bytes"
      and inst_len: "unat inst_len = length inst_bytes"
      and addr_len: "unat addr_len = length addr_bytes"
      and data_heap: "heap_bytes s data (length data_bytes) = data_bytes"
      and inst_heap: "heap_bytes s inst (length inst_bytes) = inst_bytes"
      and addr_heap: "heap_bytes s addr (length addr_bytes) = addr_bytes"
      and tgt_size: "varint_size' tgt_len s = Some tgt_n"
      and data_size: "varint_size' data_len s = Some data_n"
      and inst_size: "varint_size' inst_len s = Some inst_n"
      and addr_size: "varint_size' addr_len s = Some addr_n"
      and dlen_size: "varint_size' dlen s = Some dlen_n"
      and dlen_unat: "unat dlen = dlen_nat"
      and dlen_bytes: "varint_bytes32 dlen dlen_n = varint_encode dlen_nat"
      and tgt_bytes: "varint_bytes32 tgt_len tgt_n = varint_encode (length tgt)"
      and data_bytes: "varint_bytes32 data_len data_n = varint_encode (length data_bytes)"
      and inst_bytes: "varint_bytes32 inst_len inst_n = varint_encode (length inst_bytes)"
      and addr_bytes: "varint_bytes32 addr_len addr_n = varint_encode (length addr_bytes)"
      and b0_ok: "serialize_byte_step_ok s out out_cap 0 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b1_ok: "serialize_byte_step_ok s out out_cap 1 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b2_ok: "serialize_byte_step_ok s out out_cap 2 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b3_ok: "serialize_byte_step_ok s out out_cap 3 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b4_ok: "serialize_byte_step_ok s out out_cap 4 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b5_ok: "serialize_byte_step_ok s out out_cap 5 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and dlen_ok: "serialize_varint_step_ok s out out_cap 6 dlen dlen_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and tgt_ok: "serialize_varint_step_ok s out out_cap p_tgt tgt_len tgt_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and delta_ok: "serialize_byte_step_ok s out out_cap p_delta data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and data_len_ok: "serialize_varint_step_ok s out out_cap p_data_len data_len data_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and inst_len_ok: "serialize_varint_step_ok s out out_cap p_inst_len inst_len inst_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and addr_len_ok: "serialize_varint_step_ok s out out_cap p_addr_len addr_len addr_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and data_copy_ok: "serialize_copy_step_ok s out out_cap p_data data data_len
        inst (length inst_bytes) addr (length addr_bytes)"
      and inst_copy_ok: "serialize_copy_step_ok s out out_cap p_inst inst inst_len
        data (length data_bytes) addr (length addr_bytes)"
      and addr_copy_ok: "serialize_copy_step_ok s out out_cap p_addr addr addr_len
        data (length data_bytes) inst (length inst_bytes)"
  shows "serialize' out out_cap src_len tgt_len data data_len inst inst_len addr addr_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result p_end \<and>
                   heap_bytes t out (unat p_end) =
                     serialize src tgt data_bytes inst_bytes addr_bytes \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding serialize'_def
  apply (simp add: src_len0)
  apply runs_to_vcg
  apply (rule exI[where x = tgt_n])
  apply (simp add: tgt_size)
  apply runs_to_vcg
  apply (rule exI[where x = data_n])
  apply (simp add: data_size)
  apply runs_to_vcg
  apply (rule exI[where x = inst_n])
  apply (simp add: inst_size)
  apply runs_to_vcg
  apply (rule exI[where x = addr_n])
  apply (simp add: addr_size)
  apply runs_to_vcg
        apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
          apply (rule b0_ok)
         apply simp
        apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
         apply (rule b1_ok)
        apply simp
       apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
        apply (rule b2_ok)
       apply simp
      apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
       apply (rule b3_ok)
      apply simp
     apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
      apply (rule b4_ok)
     apply simp
    apply clarsimp
   apply runs_to_vcg
   apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
     apply (rule b5_ok)
    apply simp
   apply clarsimp
  apply runs_to_vcg
        apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
          apply (rule dlen_ok[unfolded dlen_def])
         apply simp
        apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
         apply (rule tgt_ok[unfolded p_tgt_def])
        apply simp
       apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
        apply (rule delta_ok[unfolded p_delta_def p_tgt_def])
       apply simp
      apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
       apply (rule data_len_ok[unfolded p_data_len_def])
      apply simp
     apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
      apply (rule inst_len_ok[
        unfolded p_inst_len_def p_data_len_def p_delta_def p_tgt_def])
     apply simp
    apply clarsimp
   apply runs_to_vcg
   apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
     apply (rule addr_len_ok[
       unfolded p_addr_len_def p_inst_len_def p_data_len_def p_delta_def p_tgt_def])
    apply simp
   apply clarsimp
  apply runs_to_vcg
    apply (rule runs_to_weaken[OF serialize_section_copy_step])
      apply (rule data_copy_ok[
        unfolded p_data_def p_addr_len_def p_inst_len_def p_data_len_def
          p_delta_def p_tgt_def])
     apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF serialize_section_copy_step])
      apply (rule inst_copy_ok[
        unfolded p_inst_def p_data_def p_addr_len_def p_inst_len_def
          p_data_len_def p_delta_def p_tgt_def])
     apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF serialize_section_copy_step])
      apply (rule addr_copy_ok[
        unfolded p_addr_def p_inst_def p_data_def p_addr_len_def p_inst_len_def
          p_data_len_def p_delta_def p_tgt_def])
     apply simp
  apply (clarsimp simp: p_end_def serialize_def magic_bytes_def Let_def
                          src_empty tgt_len data_len inst_len addr_len
                          data_heap inst_heap addr_heap
                          dlen_nat_def dlen_unat dlen_bytes[unfolded dlen_def]
                          tgt_bytes data_bytes inst_bytes addr_bytes
                          p_tgt_def p_delta_def p_data_len_def
                          p_inst_len_def p_addr_len_def p_data_def
                          p_inst_def p_addr_def)
  done

lemma serialize'_source_writes_serialize:
  fixes src_len tgt_len data_len inst_len addr_len :: "32 word"
    and src_n tgt_n data_n inst_n addr_n dlen_n :: "32 word"
    and src tgt data_bytes inst_bytes addr_bytes :: "byte list"
  defines "dlen_nat \<equiv>
     varint_size (length tgt) + 1 +
     varint_size (length data_bytes) +
     varint_size (length inst_bytes) +
     varint_size (length addr_bytes) +
     length data_bytes + length inst_bytes + length addr_bytes"
  defines "dlen \<equiv>
     tgt_n + 1 + data_n + inst_n + addr_n +
     data_len + inst_len + addr_len"
  defines "p_src_pos \<equiv> (6 :: 32 word) + src_n"
  defines "p_dlen \<equiv> (7 :: 32 word) + src_n"
  defines "p_tgt \<equiv> p_dlen + dlen_n"
  defines "p_delta \<equiv> p_tgt + tgt_n"
  defines "p_data_len \<equiv> (8 :: 32 word) + (src_n + (dlen_n + tgt_n))"
  defines "p_inst_len \<equiv> p_data_len + data_n"
  defines "p_addr_len \<equiv> p_inst_len + inst_n"
  defines "p_data \<equiv> p_addr_len + addr_n"
  defines "p_inst \<equiv> p_data + data_len"
  defines "p_addr \<equiv> p_inst + inst_len"
  defines "p_end \<equiv> p_addr + addr_len"
  assumes src_nonempty: "src \<noteq> []"
      and src_len: "unat src_len = length src"
      and tgt_len: "unat tgt_len = length tgt"
      and data_len: "unat data_len = length data_bytes"
      and inst_len: "unat inst_len = length inst_bytes"
      and addr_len: "unat addr_len = length addr_bytes"
      and data_heap: "heap_bytes s data (length data_bytes) = data_bytes"
      and inst_heap: "heap_bytes s inst (length inst_bytes) = inst_bytes"
      and addr_heap: "heap_bytes s addr (length addr_bytes) = addr_bytes"
      and src_size: "varint_size' src_len s = Some src_n"
      and tgt_size: "varint_size' tgt_len s = Some tgt_n"
      and data_size: "varint_size' data_len s = Some data_n"
      and inst_size: "varint_size' inst_len s = Some inst_n"
      and addr_size: "varint_size' addr_len s = Some addr_n"
      and dlen_size: "varint_size' dlen s = Some dlen_n"
      and dlen_unat: "unat dlen = dlen_nat"
      and src_bytes: "varint_bytes32 src_len src_n = varint_encode (length src)"
      and dlen_bytes: "varint_bytes32 dlen dlen_n = varint_encode dlen_nat"
      and tgt_bytes: "varint_bytes32 tgt_len tgt_n = varint_encode (length tgt)"
      and data_bytes: "varint_bytes32 data_len data_n = varint_encode (length data_bytes)"
      and inst_bytes: "varint_bytes32 inst_len inst_n = varint_encode (length inst_bytes)"
      and addr_bytes: "varint_bytes32 addr_len addr_n = varint_encode (length addr_bytes)"
      and b0_ok: "serialize_byte_step_ok s out out_cap 0 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b1_ok: "serialize_byte_step_ok s out out_cap 1 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b2_ok: "serialize_byte_step_ok s out out_cap 2 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b3_ok: "serialize_byte_step_ok s out out_cap 3 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b4_ok: "serialize_byte_step_ok s out out_cap 4 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b5_ok: "serialize_byte_step_ok s out out_cap 5 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and src_desc_len_ok: "serialize_varint_step_ok s out out_cap 6 src_len src_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and src_pos_ok: "serialize_varint_step_ok s out out_cap p_src_pos 0 1
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and dlen_ok: "serialize_varint_step_ok s out out_cap p_dlen dlen dlen_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and tgt_ok: "serialize_varint_step_ok s out out_cap p_tgt tgt_len tgt_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and delta_ok: "serialize_byte_step_ok s out out_cap p_delta data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and data_len_ok: "serialize_varint_step_ok s out out_cap p_data_len data_len data_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and inst_len_ok: "serialize_varint_step_ok s out out_cap p_inst_len inst_len inst_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and addr_len_ok: "serialize_varint_step_ok s out out_cap p_addr_len addr_len addr_n
        data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and data_copy_ok: "serialize_copy_step_ok s out out_cap p_data data data_len
        inst (length inst_bytes) addr (length addr_bytes)"
      and inst_copy_ok: "serialize_copy_step_ok s out out_cap p_inst inst inst_len
        data (length data_bytes) addr (length addr_bytes)"
      and addr_copy_ok: "serialize_copy_step_ok s out out_cap p_addr addr addr_len
        data (length data_bytes) inst (length inst_bytes)"
  shows "serialize' out out_cap src_len tgt_len data data_len inst inst_len addr addr_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result p_end \<and>
                   heap_bytes t out (unat p_end) =
                     serialize src tgt data_bytes inst_bytes addr_bytes \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have src_len_pos: "0 < src_len"
    using src_nonempty src_len by (simp add: word_less_nat_alt)
  show ?thesis
    unfolding serialize'_def
    apply (simp add: src_len_pos)
    apply runs_to_vcg
    apply (rule exI[where x = tgt_n])
    apply (simp add: tgt_size)
    apply runs_to_vcg
    apply (rule exI[where x = data_n])
    apply (simp add: data_size)
    apply runs_to_vcg
    apply (rule exI[where x = inst_n])
    apply (simp add: inst_size)
    apply runs_to_vcg
    apply (rule exI[where x = addr_n])
    apply (simp add: addr_size)
    apply runs_to_vcg
          apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
            apply (rule b0_ok)
           apply simp
          apply clarsimp
         apply runs_to_vcg
         apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
           apply (rule b1_ok)
          apply simp
         apply clarsimp
        apply runs_to_vcg
        apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
          apply (rule b2_ok)
         apply simp
        apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
         apply (rule b3_ok)
        apply simp
       apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
        apply (rule b4_ok)
       apply simp
      apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
       apply (rule b5_ok)
      apply simp
     apply clarsimp
    apply runs_to_vcg
          apply (rule runs_to_weaken[OF serialize_source_descriptor_varint_step])
            apply (rule src_desc_len_ok)
           apply simp
          apply clarsimp
         apply runs_to_vcg
         apply (rule runs_to_weaken[OF serialize_source_descriptor_varint_step])
           apply (rule src_pos_ok[unfolded p_src_pos_def])
          apply simp
         apply clarsimp
        apply runs_to_vcg
        apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
          apply (rule dlen_ok[unfolded p_dlen_def p_src_pos_def dlen_def])
         apply simp
        apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
         apply (rule tgt_ok[unfolded p_tgt_def p_dlen_def p_src_pos_def])
        apply simp
       apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF serialize_fixed_header_byte_step])
        apply (rule delta_ok[unfolded p_delta_def p_tgt_def p_dlen_def p_src_pos_def])
       apply simp
      apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
       apply (rule data_len_ok[
         unfolded p_data_len_def p_delta_def p_tgt_def p_dlen_def p_src_pos_def])
      apply simp
     apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
      apply (rule inst_len_ok[
        unfolded p_inst_len_def p_data_len_def p_delta_def p_tgt_def p_dlen_def
          p_src_pos_def])
     apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF serialize_delta_header_varint_step])
      apply (rule addr_len_ok[
        unfolded p_addr_len_def p_inst_len_def p_data_len_def p_delta_def p_tgt_def
          p_dlen_def p_src_pos_def])
     apply simp
    apply clarsimp
    apply runs_to_vcg
      apply (rule runs_to_weaken[OF serialize_section_copy_step])
        apply (rule data_copy_ok[
          unfolded p_data_def p_addr_len_def p_inst_len_def p_data_len_def
            p_delta_def p_tgt_def p_dlen_def p_src_pos_def])
       apply simp
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF serialize_section_copy_step])
        apply (rule inst_copy_ok[
          unfolded p_inst_def p_data_def p_addr_len_def p_inst_len_def
            p_data_len_def p_delta_def p_tgt_def p_dlen_def p_src_pos_def])
       apply simp
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF serialize_section_copy_step])
        apply (rule addr_copy_ok[
          unfolded p_addr_def p_inst_def p_data_def p_addr_len_def p_inst_len_def
            p_data_len_def p_delta_def p_tgt_def p_dlen_def p_src_pos_def])
       apply simp
      apply (clarsimp simp: p_end_def serialize_def magic_bytes_def Let_def
                            src_nonempty src_len tgt_len data_len inst_len addr_len
                            data_heap inst_heap addr_heap
                            dlen_nat_def dlen_unat dlen_bytes[unfolded dlen_def]
                            src_bytes tgt_bytes data_bytes inst_bytes addr_bytes
                            p_src_pos_def p_dlen_def p_tgt_def p_delta_def
                            p_data_len_def p_inst_len_def p_addr_len_def
                            p_data_def p_inst_def p_addr_def)
    done
qed

lemma serialize'_writes_serialize:
  fixes src_len tgt_len data_len inst_len addr_len :: "32 word"
    and src_n tgt_n data_n inst_n addr_n dlen_n :: "32 word"
    and src tgt data_bytes inst_bytes addr_bytes :: "byte list"
  defines "dlen_nat \<equiv>
     varint_size (length tgt) + 1 +
     varint_size (length data_bytes) +
     varint_size (length inst_bytes) +
     varint_size (length addr_bytes) +
     length data_bytes + length inst_bytes + length addr_bytes"
  defines "dlen \<equiv>
     tgt_n + 1 + data_n + inst_n + addr_n +
     data_len + inst_len + addr_len"
  defines "p0_tgt \<equiv> (6 :: 32 word) + dlen_n"
  defines "p0_delta \<equiv> p0_tgt + tgt_n"
  defines "p0_data_len \<equiv> (7 :: 32 word) + (dlen_n + tgt_n)"
  defines "p0_inst_len \<equiv> p0_data_len + data_n"
  defines "p0_addr_len \<equiv> p0_inst_len + inst_n"
  defines "p0_data \<equiv> p0_addr_len + addr_n"
  defines "p0_inst \<equiv> p0_data + data_len"
  defines "p0_addr \<equiv> p0_inst + inst_len"
  defines "p0_end \<equiv> p0_addr + addr_len"
  defines "p1_src_pos \<equiv> (6 :: 32 word) + src_n"
  defines "p1_dlen \<equiv> (7 :: 32 word) + src_n"
  defines "p1_tgt \<equiv> p1_dlen + dlen_n"
  defines "p1_delta \<equiv> p1_tgt + tgt_n"
  defines "p1_data_len \<equiv> (8 :: 32 word) + (src_n + (dlen_n + tgt_n))"
  defines "p1_inst_len \<equiv> p1_data_len + data_n"
  defines "p1_addr_len \<equiv> p1_inst_len + inst_n"
  defines "p1_data \<equiv> p1_addr_len + addr_n"
  defines "p1_inst \<equiv> p1_data + data_len"
  defines "p1_addr \<equiv> p1_inst + inst_len"
  defines "p1_end \<equiv> p1_addr + addr_len"
  defines "p_end \<equiv> if src = [] then p0_end else p1_end"
  assumes src_len: "unat src_len = length src"
      and tgt_len: "unat tgt_len = length tgt"
      and data_len: "unat data_len = length data_bytes"
      and inst_len: "unat inst_len = length inst_bytes"
      and addr_len: "unat addr_len = length addr_bytes"
      and data_heap: "heap_bytes s data (length data_bytes) = data_bytes"
      and inst_heap: "heap_bytes s inst (length inst_bytes) = inst_bytes"
      and addr_heap: "heap_bytes s addr (length addr_bytes) = addr_bytes"
      and src_size: "src \<noteq> [] \<Longrightarrow> varint_size' src_len s = Some src_n"
      and tgt_size: "varint_size' tgt_len s = Some tgt_n"
      and data_size: "varint_size' data_len s = Some data_n"
      and inst_size: "varint_size' inst_len s = Some inst_n"
      and addr_size: "varint_size' addr_len s = Some addr_n"
      and dlen_size: "varint_size' dlen s = Some dlen_n"
      and dlen_unat: "unat dlen = dlen_nat"
      and src_bytes: "src \<noteq> [] \<Longrightarrow>
        varint_bytes32 src_len src_n = varint_encode (length src)"
      and dlen_bytes: "varint_bytes32 dlen dlen_n = varint_encode dlen_nat"
      and tgt_bytes: "varint_bytes32 tgt_len tgt_n = varint_encode (length tgt)"
      and data_bytes: "varint_bytes32 data_len data_n = varint_encode (length data_bytes)"
      and inst_bytes: "varint_bytes32 inst_len inst_n = varint_encode (length inst_bytes)"
      and addr_bytes: "varint_bytes32 addr_len addr_n = varint_encode (length addr_bytes)"
      and b0_ok: "serialize_byte_step_ok s out out_cap 0 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b1_ok: "serialize_byte_step_ok s out out_cap 1 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b2_ok: "serialize_byte_step_ok s out out_cap 2 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b3_ok: "serialize_byte_step_ok s out out_cap 3 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b4_ok: "serialize_byte_step_ok s out out_cap 4 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and b5_ok: "serialize_byte_step_ok s out out_cap 5 data (length data_bytes)
        inst (length inst_bytes) addr (length addr_bytes)"
      and no_dlen_ok: "src = [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap 6 dlen dlen_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and no_tgt_ok: "src = [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p0_tgt tgt_len tgt_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and no_delta_ok: "src = [] \<Longrightarrow>
        serialize_byte_step_ok s out out_cap p0_delta data (length data_bytes)
          inst (length inst_bytes) addr (length addr_bytes)"
      and no_data_len_ok: "src = [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p0_data_len data_len data_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and no_inst_len_ok: "src = [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p0_inst_len inst_len inst_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and no_addr_len_ok: "src = [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p0_addr_len addr_len addr_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and no_data_copy_ok: "src = [] \<Longrightarrow>
        serialize_copy_step_ok s out out_cap p0_data data data_len
          inst (length inst_bytes) addr (length addr_bytes)"
      and no_inst_copy_ok: "src = [] \<Longrightarrow>
        serialize_copy_step_ok s out out_cap p0_inst inst inst_len
          data (length data_bytes) addr (length addr_bytes)"
      and no_addr_copy_ok: "src = [] \<Longrightarrow>
        serialize_copy_step_ok s out out_cap p0_addr addr addr_len
          data (length data_bytes) inst (length inst_bytes)"
      and src_desc_len_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap 6 src_len src_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and src_pos_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p1_src_pos 0 1
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and src_dlen_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p1_dlen dlen dlen_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and src_tgt_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p1_tgt tgt_len tgt_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and src_delta_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_byte_step_ok s out out_cap p1_delta data (length data_bytes)
          inst (length inst_bytes) addr (length addr_bytes)"
      and src_data_len_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p1_data_len data_len data_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and src_inst_len_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p1_inst_len inst_len inst_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and src_addr_len_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_varint_step_ok s out out_cap p1_addr_len addr_len addr_n
          data (length data_bytes) inst (length inst_bytes) addr (length addr_bytes)"
      and src_data_copy_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_copy_step_ok s out out_cap p1_data data data_len
          inst (length inst_bytes) addr (length addr_bytes)"
      and src_inst_copy_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_copy_step_ok s out out_cap p1_inst inst inst_len
          data (length data_bytes) addr (length addr_bytes)"
      and src_addr_copy_ok: "src \<noteq> [] \<Longrightarrow>
        serialize_copy_step_ok s out out_cap p1_addr addr addr_len
          data (length data_bytes) inst (length inst_bytes)"
  shows "serialize' out out_cap src_len tgt_len data data_len inst inst_len addr addr_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result p_end \<and>
                   heap_bytes t out (unat p_end) =
                     serialize src tgt data_bytes inst_bytes addr_bytes \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof (cases "src = []")
  case True
  have src_len0: "src_len = 0"
    using True src_len by (simp add: unat_eq_0)
  show ?thesis
    apply (simp add: p_end_def True p0_end_def p0_addr_def p0_inst_def
                     p0_data_def p0_addr_len_def p0_inst_len_def
	                     p0_data_len_def p0_delta_def p0_tgt_def)
    apply (rule serialize'_no_source_writes_serialize)
                                    apply (insert tgt_len data_len inst_len
                                      addr_len data_heap inst_heap addr_heap
                                      tgt_size data_size inst_size addr_size
                                      dlen_size dlen_unat dlen_bytes tgt_bytes
                                      data_bytes inst_bytes addr_bytes
                                      b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok
                                      no_dlen_ok[OF True] no_tgt_ok[OF True]
                                      no_delta_ok[OF True]
                                      no_data_len_ok[OF True]
                                      no_inst_len_ok[OF True]
                                      no_addr_len_ok[OF True]
                                      no_data_copy_ok[OF True]
                                      no_inst_copy_ok[OF True]
                                      no_addr_copy_ok[OF True])
                                     apply (simp_all add: dlen_nat_def dlen_def
                                      p0_tgt_def p0_delta_def p0_data_len_def
                                      p0_inst_len_def p0_addr_len_def p0_data_def
                                      p0_inst_def p0_addr_def p0_end_def
                                      True src_len0 tgt_len data_len inst_len
                                      addr_len data_heap inst_heap addr_heap
                                      tgt_size data_size inst_size addr_size
                                      dlen_size dlen_unat dlen_bytes tgt_bytes
                                      data_bytes inst_bytes addr_bytes
                                      b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok
                                      no_dlen_ok[OF True] no_tgt_ok[OF True]
                                      no_delta_ok[OF True]
                                      no_data_len_ok[OF True]
                                      no_inst_len_ok[OF True]
                                      no_addr_len_ok[OF True]
                                      no_data_copy_ok[OF True]
                                      no_inst_copy_ok[OF True]
                                      no_addr_copy_ok[OF True])
    done
next
  case False
  show ?thesis
    apply (simp add: p_end_def False p1_end_def p1_addr_def p1_inst_def
                     p1_data_def p1_addr_len_def p1_inst_len_def
                     p1_data_len_def p1_delta_def p1_tgt_def p1_dlen_def
	                     p1_src_pos_def)
    apply (rule serialize'_source_writes_serialize)
                                     apply (insert src_len tgt_len data_len
                                       inst_len addr_len data_heap inst_heap
                                       addr_heap src_size[OF False] tgt_size
                                       data_size inst_size addr_size dlen_size
                                       dlen_unat src_bytes[OF False] dlen_bytes
                                       tgt_bytes data_bytes inst_bytes addr_bytes
                                       b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok
                                       src_desc_len_ok[OF False]
                                       src_pos_ok[OF False]
                                       src_dlen_ok[OF False]
                                       src_tgt_ok[OF False]
                                       src_delta_ok[OF False]
                                       src_data_len_ok[OF False]
                                       src_inst_len_ok[OF False]
                                       src_addr_len_ok[OF False]
                                       src_data_copy_ok[OF False]
                                       src_inst_copy_ok[OF False]
                                       src_addr_copy_ok[OF False])
                                      apply (simp_all add: dlen_nat_def dlen_def
                                        p1_src_pos_def p1_dlen_def p1_tgt_def
                                        p1_delta_def p1_data_len_def
                                        p1_inst_len_def p1_addr_len_def
                                        p1_data_def p1_inst_def p1_addr_def
                                        p1_end_def False src_len tgt_len
                                        data_len inst_len addr_len data_heap
                                        inst_heap addr_heap src_size[OF False]
                                        tgt_size data_size inst_size addr_size
                                        dlen_size dlen_unat src_bytes[OF False]
                                        dlen_bytes tgt_bytes data_bytes
                                        inst_bytes addr_bytes b0_ok b1_ok b2_ok
                                        b3_ok b4_ok b5_ok
                                        src_desc_len_ok[OF False]
                                        src_pos_ok[OF False]
                                        src_dlen_ok[OF False]
                                        src_tgt_ok[OF False]
                                        src_delta_ok[OF False]
                                        src_data_len_ok[OF False]
                                        src_inst_len_ok[OF False]
                                        src_addr_len_ok[OF False]
                                        src_data_copy_ok[OF False]
                                        src_inst_copy_ok[OF False]
                                        src_addr_copy_ok[OF False])
    done
qed

definition encoder_input_rel ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> bool" where
  "encoder_input_rel s src src_len tgt tgt_len src_bytes tgt_bytes \<longleftrightarrow>
     heap_bytes s src (unat src_len) = src_bytes \<and>
     heap_bytes s tgt (unat tgt_len) = tgt_bytes \<and>
     unat src_len = length src_bytes \<and>
     unat tgt_len = length tgt_bytes"

definition encoder_buffers_ok ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> bool" where
  "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
      pending pending_cap data data_cap inst inst_cap addr addr_cap \<longleftrightarrow>
     buf_valid s out (unat out_cap) \<and>
     buf_valid s src (unat src_len) \<and>
     buf_valid s tgt (unat tgt_len) \<and>
     buf_valid s pending (unat pending_cap) \<and>
     buf_valid s data (unat data_cap) \<and>
     buf_valid s inst (unat inst_cap) \<and>
     buf_valid s addr (unat addr_cap) \<and>
     ptr_range_distinct out (unat out_cap) \<and>
     ptr_range_distinct src (unat src_len) \<and>
     ptr_range_distinct tgt (unat tgt_len) \<and>
     ptr_range_distinct pending (unat pending_cap) \<and>
     ptr_range_distinct data (unat data_cap) \<and>
     ptr_range_distinct inst (unat inst_cap) \<and>
     ptr_range_distinct addr (unat addr_cap) \<and>
     unat tgt_len \<le> unat pending_cap \<and>
     unat tgt_len + 64 \<le> unat data_cap \<and>
     unat tgt_len + 64 \<le> unat inst_cap \<and>
     unat tgt_len + 64 \<le> unat addr_cap \<and>
     bufs_disjoint out (unat out_cap) src (unat src_len) \<and>
     bufs_disjoint out (unat out_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint out (unat out_cap) pending (unat pending_cap) \<and>
     bufs_disjoint out (unat out_cap) data (unat data_cap) \<and>
     bufs_disjoint out (unat out_cap) inst (unat inst_cap) \<and>
     bufs_disjoint out (unat out_cap) addr (unat addr_cap) \<and>
     bufs_disjoint pending (unat pending_cap) src (unat src_len) \<and>
     bufs_disjoint pending (unat pending_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint pending (unat pending_cap) data (unat data_cap) \<and>
     bufs_disjoint pending (unat pending_cap) inst (unat inst_cap) \<and>
     bufs_disjoint pending (unat pending_cap) addr (unat addr_cap) \<and>
     bufs_disjoint data (unat data_cap) src (unat src_len) \<and>
     bufs_disjoint data (unat data_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint data (unat data_cap) inst (unat inst_cap) \<and>
     bufs_disjoint data (unat data_cap) addr (unat addr_cap) \<and>
     bufs_disjoint inst (unat inst_cap) src (unat src_len) \<and>
	     bufs_disjoint inst (unat inst_cap) tgt (unat tgt_len) \<and>
	     bufs_disjoint inst (unat inst_cap) addr (unat addr_cap) \<and>
	     bufs_disjoint addr (unat addr_cap) src (unat src_len) \<and>
	     bufs_disjoint addr (unat addr_cap) tgt (unat tgt_len)"

lemma encoder_buffers_ok_heap_typing_eq:
  assumes typing: "heap_typing t = heap_typing s"
      and buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
  shows "encoder_buffers_ok t out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
  using typing buffers
  by (simp add: encoder_buffers_ok_def buf_valid_def)

lemma word_sub_not_less_of_unat_add_le:
  fixes pos len cap :: "32 word"
  assumes range: "unat pos + unat len \<le> unat cap"
  shows "\<not> cap - pos < len"
  using range by unat_arith

lemma unat_add_lt2p_of_le_unat32:
  fixes pos len cap :: "32 word"
  assumes range: "unat pos + unat len \<le> unat cap"
  shows "unat pos + unat len < 2 ^ 32"
proof -
  have "unat cap < 2 ^ 32"
    using unat_lt2p[of cap] by simp
  thus ?thesis
    using range by linarith
qed

lemma bufs_disjoint_word_range_rightD_word:
  fixes pos len i :: "32 word"
  assumes disj: "bufs_disjoint p pn q qn"
      and k_lt: "k < pn"
      and i_lt: "i < len"
      and no_overflow: "unat pos + unat len < 2 ^ 32"
      and range: "unat pos + unat len \<le> qn"
  shows "p +\<^sub>p int k \<noteq> q +\<^sub>p uint (pos + i)"
proof -
  have i_nat_lt: "unat i < unat len"
    using i_lt by (simp add: word_less_nat_alt)
  have word_eq: "pos + of_nat (unat i) = pos + i"
    by (simp add: word_unat.Rep_inverse)
  show ?thesis
    using bufs_disjoint_word_range_rightD[OF disj k_lt i_nat_lt no_overflow range]
    by (simp add: word_eq)
qed

lemma bufs_disjoint_word_rangesD_word:
  fixes p_pos p_len q_pos q_len i j :: "32 word"
  assumes disj: "bufs_disjoint p pn q qn"
      and i_lt: "i < p_len"
      and j_lt: "j < q_len"
      and p_no_overflow: "unat p_pos + unat p_len < 2 ^ 32"
      and q_no_overflow: "unat q_pos + unat q_len < 2 ^ 32"
      and p_range: "unat p_pos + unat p_len \<le> pn"
      and q_range: "unat q_pos + unat q_len \<le> qn"
  shows "p +\<^sub>p uint (p_pos + i) \<noteq> q +\<^sub>p uint (q_pos + j)"
proof -
  have i_nat_lt: "unat i < unat p_len"
    using i_lt by (simp add: word_less_nat_alt)
  have j_nat_lt: "unat j < unat q_len"
    using j_lt by (simp add: word_less_nat_alt)
  have p_word_eq: "p_pos + of_nat (unat i) = p_pos + i"
    by (simp add: word_unat.Rep_inverse)
  have q_word_eq: "q_pos + of_nat (unat j) = q_pos + j"
    by (simp add: word_unat.Rep_inverse)
  show ?thesis
    using bufs_disjoint_word_rangesD[
      OF disj i_nat_lt j_nat_lt p_no_overflow q_no_overflow p_range q_range]
    by (simp add: p_word_eq q_word_eq)
qed

lemma serialize_byte_step_ok_from_encoder_buffers:
  assumes buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and pos_lt: "unat pos < unat out_cap"
      and data_range: "data_n \<le> unat data_cap"
      and inst_range: "inst_n \<le> unat inst_cap"
      and addr_range: "addr_n \<le> unat addr_cap"
  shows "serialize_byte_step_ok s out out_cap pos data data_n inst inst_n addr addr_n"
proof -
  have out_valid: "buf_valid s out (unat out_cap)"
    and out_dist: "ptr_range_distinct out (unat out_cap)"
    and out_data: "bufs_disjoint out (unat out_cap) data (unat data_cap)"
    and out_inst: "bufs_disjoint out (unat out_cap) inst (unat inst_cap)"
    and out_addr: "bufs_disjoint out (unat out_cap) addr (unat addr_cap)"
    using buffers by (simp_all add: encoder_buffers_ok_def)
  show ?thesis
    unfolding serialize_byte_step_ok_def
  proof (intro conjI allI impI)
    show "pos < out_cap"
      using pos_lt by (simp add: word_less_nat_alt)
    show "ptr_valid (heap_typing s) (out +\<^sub>p uint pos)"
      by (rule buf_valid_uintD[OF out_valid pos_lt])
    show "ptr_range_distinct out (Suc (unat pos))"
      by (rule ptr_range_distinct_mono[OF out_dist]) (use pos_lt in simp)
  next
    fix i
    assume i_lt: "i < data_n"
    show "data +\<^sub>p int i \<noteq> out +\<^sub>p uint pos"
    proof -
      have data_out: "bufs_disjoint data (unat data_cap) out (unat out_cap)"
        using out_data by (simp add: bufs_disjoint_sym)
      show ?thesis
        by (rule bufs_disjoint_word_point_rightD[OF data_out _ pos_lt])
          (use i_lt data_range in simp)
    qed
  next
    fix i
    assume i_lt: "i < inst_n"
    show "inst +\<^sub>p int i \<noteq> out +\<^sub>p uint pos"
    proof -
      have inst_out: "bufs_disjoint inst (unat inst_cap) out (unat out_cap)"
        using out_inst by (simp add: bufs_disjoint_sym)
      show ?thesis
        by (rule bufs_disjoint_word_point_rightD[OF inst_out _ pos_lt])
          (use i_lt inst_range in simp)
    qed
  next
    fix i
    assume i_lt: "i < addr_n"
    show "addr +\<^sub>p int i \<noteq> out +\<^sub>p uint pos"
    proof -
      have addr_out: "bufs_disjoint addr (unat addr_cap) out (unat out_cap)"
        using out_addr by (simp add: bufs_disjoint_sym)
      show ?thesis
        by (rule bufs_disjoint_word_point_rightD[OF addr_out _ pos_lt])
          (use i_lt addr_range in simp)
    qed
  qed
qed

lemma serialize_varint_step_ok_from_encoder_buffers:
  assumes buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and size: "varint_size' v s = Some n"
      and out_range: "unat pos + unat n \<le> unat out_cap"
      and data_range: "data_n \<le> unat data_cap"
      and inst_range: "inst_n \<le> unat inst_cap"
      and addr_range: "addr_n \<le> unat addr_cap"
  shows "serialize_varint_step_ok s out out_cap pos v n data data_n inst inst_n addr addr_n"
proof -
  have out_valid: "buf_valid s out (unat out_cap)"
    and out_dist: "ptr_range_distinct out (unat out_cap)"
    and out_data: "bufs_disjoint out (unat out_cap) data (unat data_cap)"
    and out_inst: "bufs_disjoint out (unat out_cap) inst (unat inst_cap)"
    and out_addr: "bufs_disjoint out (unat out_cap) addr (unat addr_cap)"
    using buffers by (simp_all add: encoder_buffers_ok_def)
  have no_overflow: "unat pos + unat n < 2 ^ 32"
    by (rule unat_add_lt2p_of_le_unat32[OF out_range])
  have fits: "\<not> out_cap - pos < n"
    by (rule word_sub_not_less_of_unat_add_le[OF out_range])
  show ?thesis
    unfolding serialize_varint_step_ok_def
  proof (intro conjI allI impI)
    show "varint_size' v s = Some n"
      by (rule size)
    show "\<not> out_cap - pos < n"
      by (rule fits)
  next
    fix j
    assume j_lt: "j < unat n"
    show "ptr_valid (heap_typing s) (out +\<^sub>p uint (pos + of_nat j))"
      by (rule buf_valid_word_rangeD[OF out_valid j_lt no_overflow out_range])
  next
    fix i j
    assume i_lt: "i < unat n"
      and j_lt: "j < unat n"
      and neq: "i \<noteq> j"
    show "out +\<^sub>p uint (pos + of_nat i) \<noteq> out +\<^sub>p uint (pos + of_nat j)"
    proof
      assume eq: "out +\<^sub>p uint (pos + of_nat i) =
        out +\<^sub>p uint (pos + of_nat j)"
      have "i = j"
        by (rule ptr_range_distinct_word_range_inj[
            OF out_dist no_overflow out_range i_lt j_lt eq])
      thus False using neq by simp
    qed
  next
    fix k i
    assume k_lt: "k < unat pos"
      and i_lt: "i < n"
    show "out +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule ptr_range_distinct_word_prefix_disj[
          OF out_dist no_overflow out_range k_lt i_lt])
  next
    show "unat pos + unat n < 2 ^ 32"
      by (rule no_overflow)
  next
    fix k i
    assume k_lt: "k < data_n"
      and i_lt: "i < n"
    have data_out: "bufs_disjoint data (unat data_cap) out (unat out_cap)"
      using out_data by (simp add: bufs_disjoint_sym)
    show "data +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF data_out _ i_lt no_overflow out_range])
        (use k_lt data_range in simp)
  next
    fix k i
    assume k_lt: "k < inst_n"
      and i_lt: "i < n"
    have inst_out: "bufs_disjoint inst (unat inst_cap) out (unat out_cap)"
      using out_inst by (simp add: bufs_disjoint_sym)
    show "inst +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF inst_out _ i_lt no_overflow out_range])
        (use k_lt inst_range in simp)
  next
    fix k i
    assume k_lt: "k < addr_n"
      and i_lt: "i < n"
    have addr_out: "bufs_disjoint addr (unat addr_cap) out (unat out_cap)"
      using out_addr by (simp add: bufs_disjoint_sym)
    show "addr +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF addr_out _ i_lt no_overflow out_range])
        (use k_lt addr_range in simp)
  qed
qed

lemma serialize_data_copy_step_ok_from_encoder_buffers:
  assumes buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and out_range: "unat pos + unat data_len \<le> unat out_cap"
      and data_range: "unat data_len \<le> unat data_cap"
      and inst_range: "inst_n \<le> unat inst_cap"
      and addr_range: "addr_n \<le> unat addr_cap"
  shows "serialize_copy_step_ok s out out_cap pos data data_len inst inst_n addr addr_n"
proof -
  have out_valid: "buf_valid s out (unat out_cap)"
    and data_valid: "buf_valid s data (unat data_cap)"
    and out_dist: "ptr_range_distinct out (unat out_cap)"
    and out_data: "bufs_disjoint out (unat out_cap) data (unat data_cap)"
    and out_inst: "bufs_disjoint out (unat out_cap) inst (unat inst_cap)"
    and out_addr: "bufs_disjoint out (unat out_cap) addr (unat addr_cap)"
    using buffers by (simp_all add: encoder_buffers_ok_def)
  have out_no_overflow: "unat pos + unat data_len < 2 ^ 32"
    by (rule unat_add_lt2p_of_le_unat32[OF out_range])
  have data_no_overflow: "unat (0 :: 32 word) + unat data_len < 2 ^ 32"
    using unat_lt2p[of data_len] by simp
  have data_range0: "unat (0 :: 32 word) + unat data_len \<le> unat data_cap"
    using data_range by simp
  have fits: "\<not> out_cap - pos < data_len"
    by (rule word_sub_not_less_of_unat_add_le[OF out_range])
  show ?thesis
    unfolding serialize_copy_step_ok_def
  proof (intro conjI allI impI)
    show "\<not> out_cap - pos < data_len"
      by (rule fits)
  next
    fix j
    assume j_lt: "j < unat data_len"
    show "ptr_valid (heap_typing s) (out +\<^sub>p uint (pos + of_nat j))"
      by (rule buf_valid_word_rangeD[OF out_valid j_lt out_no_overflow out_range])
  next
    fix j
    assume j_lt: "j < unat data_len"
    show "ptr_valid (heap_typing s) (data +\<^sub>p uint ((0::32 word) + of_nat j))"
      by (rule buf_valid_word_rangeD[
          where base = "0 :: 32 word" and len = data_len,
          OF data_valid j_lt data_no_overflow data_range0])
  next
    fix i j
    assume i_lt: "i < unat data_len"
      and j_lt: "j < unat data_len"
    show "out +\<^sub>p uint (pos + of_nat i) \<noteq>
      data +\<^sub>p uint ((0::32 word) + of_nat j)"
      by (rule bufs_disjoint_word_rangesD[
          where p_pos = pos and p_len = data_len
            and q_pos = "0 :: 32 word" and q_len = data_len,
          OF out_data i_lt j_lt out_no_overflow data_no_overflow
            out_range data_range0])
  next
    fix i j
    assume i_lt: "i < unat data_len"
      and j_lt: "j < unat data_len"
      and neq: "i \<noteq> j"
    show "out +\<^sub>p uint (pos + of_nat i) \<noteq>
      out +\<^sub>p uint (pos + of_nat j)"
    proof
      assume eq: "out +\<^sub>p uint (pos + of_nat i) =
        out +\<^sub>p uint (pos + of_nat j)"
      have "i = j"
        by (rule ptr_range_distinct_word_range_inj[
            OF out_dist out_no_overflow out_range i_lt j_lt eq])
      thus False using neq by simp
    qed
  next
    fix k i
    assume k_lt: "k < unat pos"
      and i_lt: "i < data_len"
    show "out +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule ptr_range_distinct_word_prefix_disj[
          OF out_dist out_no_overflow out_range k_lt i_lt])
  next
    show "unat pos + unat data_len < 2 ^ 32"
      by (rule out_no_overflow)
  next
    fix k i
    assume k_lt: "k < inst_n"
      and i_lt: "i < data_len"
    have inst_out: "bufs_disjoint inst (unat inst_cap) out (unat out_cap)"
      using out_inst by (simp add: bufs_disjoint_sym)
    show "inst +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF inst_out _ i_lt out_no_overflow out_range])
        (use k_lt inst_range in simp)
  next
    fix k i
    assume k_lt: "k < addr_n"
      and i_lt: "i < data_len"
    have addr_out: "bufs_disjoint addr (unat addr_cap) out (unat out_cap)"
      using out_addr by (simp add: bufs_disjoint_sym)
    show "addr +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF addr_out _ i_lt out_no_overflow out_range])
        (use k_lt addr_range in simp)
  qed
qed

lemma serialize_inst_copy_step_ok_from_encoder_buffers:
  assumes buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and out_range: "unat pos + unat inst_len \<le> unat out_cap"
      and inst_range: "unat inst_len \<le> unat inst_cap"
      and data_range: "data_n \<le> unat data_cap"
      and addr_range: "addr_n \<le> unat addr_cap"
  shows "serialize_copy_step_ok s out out_cap pos inst inst_len data data_n addr addr_n"
proof -
  have out_valid: "buf_valid s out (unat out_cap)"
    and inst_valid: "buf_valid s inst (unat inst_cap)"
    and out_dist: "ptr_range_distinct out (unat out_cap)"
    and out_data: "bufs_disjoint out (unat out_cap) data (unat data_cap)"
    and out_inst: "bufs_disjoint out (unat out_cap) inst (unat inst_cap)"
    and out_addr: "bufs_disjoint out (unat out_cap) addr (unat addr_cap)"
    using buffers by (simp_all add: encoder_buffers_ok_def)
  have out_no_overflow: "unat pos + unat inst_len < 2 ^ 32"
    by (rule unat_add_lt2p_of_le_unat32[OF out_range])
  have inst_no_overflow: "unat (0 :: 32 word) + unat inst_len < 2 ^ 32"
    using unat_lt2p[of inst_len] by simp
  have inst_range0: "unat (0 :: 32 word) + unat inst_len \<le> unat inst_cap"
    using inst_range by simp
  have fits: "\<not> out_cap - pos < inst_len"
    by (rule word_sub_not_less_of_unat_add_le[OF out_range])
  show ?thesis
    unfolding serialize_copy_step_ok_def
  proof (intro conjI allI impI)
    show "\<not> out_cap - pos < inst_len"
      by (rule fits)
  next
    fix j
    assume j_lt: "j < unat inst_len"
    show "ptr_valid (heap_typing s) (out +\<^sub>p uint (pos + of_nat j))"
      by (rule buf_valid_word_rangeD[OF out_valid j_lt out_no_overflow out_range])
  next
    fix j
    assume j_lt: "j < unat inst_len"
    show "ptr_valid (heap_typing s) (inst +\<^sub>p uint ((0::32 word) + of_nat j))"
      by (rule buf_valid_word_rangeD[
          where base = "0 :: 32 word" and len = inst_len,
          OF inst_valid j_lt inst_no_overflow inst_range0])
  next
    fix i j
    assume i_lt: "i < unat inst_len"
      and j_lt: "j < unat inst_len"
    show "out +\<^sub>p uint (pos + of_nat i) \<noteq>
      inst +\<^sub>p uint ((0::32 word) + of_nat j)"
      by (rule bufs_disjoint_word_rangesD[
          where p_pos = pos and p_len = inst_len
            and q_pos = "0 :: 32 word" and q_len = inst_len,
          OF out_inst i_lt j_lt out_no_overflow inst_no_overflow
            out_range inst_range0])
  next
    fix i j
    assume i_lt: "i < unat inst_len"
      and j_lt: "j < unat inst_len"
      and neq: "i \<noteq> j"
    show "out +\<^sub>p uint (pos + of_nat i) \<noteq>
      out +\<^sub>p uint (pos + of_nat j)"
    proof
      assume eq: "out +\<^sub>p uint (pos + of_nat i) =
        out +\<^sub>p uint (pos + of_nat j)"
      have "i = j"
        by (rule ptr_range_distinct_word_range_inj[
            OF out_dist out_no_overflow out_range i_lt j_lt eq])
      thus False using neq by simp
    qed
  next
    fix k i
    assume k_lt: "k < unat pos"
      and i_lt: "i < inst_len"
    show "out +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule ptr_range_distinct_word_prefix_disj[
          OF out_dist out_no_overflow out_range k_lt i_lt])
  next
    show "unat pos + unat inst_len < 2 ^ 32"
      by (rule out_no_overflow)
  next
    fix k i
    assume k_lt: "k < data_n"
      and i_lt: "i < inst_len"
    have data_out: "bufs_disjoint data (unat data_cap) out (unat out_cap)"
      using out_data by (simp add: bufs_disjoint_sym)
    show "data +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF data_out _ i_lt out_no_overflow out_range])
        (use k_lt data_range in simp)
  next
    fix k i
    assume k_lt: "k < addr_n"
      and i_lt: "i < inst_len"
    have addr_out: "bufs_disjoint addr (unat addr_cap) out (unat out_cap)"
      using out_addr by (simp add: bufs_disjoint_sym)
    show "addr +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF addr_out _ i_lt out_no_overflow out_range])
        (use k_lt addr_range in simp)
  qed
qed

lemma serialize_addr_copy_step_ok_from_encoder_buffers:
  assumes buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and out_range: "unat pos + unat addr_len \<le> unat out_cap"
      and addr_range: "unat addr_len \<le> unat addr_cap"
      and data_range: "data_n \<le> unat data_cap"
      and inst_range: "inst_n \<le> unat inst_cap"
  shows "serialize_copy_step_ok s out out_cap pos addr addr_len data data_n inst inst_n"
proof -
  have out_valid: "buf_valid s out (unat out_cap)"
    and addr_valid: "buf_valid s addr (unat addr_cap)"
    and out_dist: "ptr_range_distinct out (unat out_cap)"
    and out_data: "bufs_disjoint out (unat out_cap) data (unat data_cap)"
    and out_inst: "bufs_disjoint out (unat out_cap) inst (unat inst_cap)"
    and out_addr: "bufs_disjoint out (unat out_cap) addr (unat addr_cap)"
    using buffers by (simp_all add: encoder_buffers_ok_def)
  have out_no_overflow: "unat pos + unat addr_len < 2 ^ 32"
    by (rule unat_add_lt2p_of_le_unat32[OF out_range])
  have addr_no_overflow: "unat (0 :: 32 word) + unat addr_len < 2 ^ 32"
    using unat_lt2p[of addr_len] by simp
  have addr_range0: "unat (0 :: 32 word) + unat addr_len \<le> unat addr_cap"
    using addr_range by simp
  have fits: "\<not> out_cap - pos < addr_len"
    by (rule word_sub_not_less_of_unat_add_le[OF out_range])
  show ?thesis
    unfolding serialize_copy_step_ok_def
  proof (intro conjI allI impI)
    show "\<not> out_cap - pos < addr_len"
      by (rule fits)
  next
    fix j
    assume j_lt: "j < unat addr_len"
    show "ptr_valid (heap_typing s) (out +\<^sub>p uint (pos + of_nat j))"
      by (rule buf_valid_word_rangeD[OF out_valid j_lt out_no_overflow out_range])
  next
    fix j
    assume j_lt: "j < unat addr_len"
    show "ptr_valid (heap_typing s) (addr +\<^sub>p uint ((0::32 word) + of_nat j))"
      by (rule buf_valid_word_rangeD[
          where base = "0 :: 32 word" and len = addr_len,
          OF addr_valid j_lt addr_no_overflow addr_range0])
  next
    fix i j
    assume i_lt: "i < unat addr_len"
      and j_lt: "j < unat addr_len"
    show "out +\<^sub>p uint (pos + of_nat i) \<noteq>
      addr +\<^sub>p uint ((0::32 word) + of_nat j)"
      by (rule bufs_disjoint_word_rangesD[
          where p_pos = pos and p_len = addr_len
            and q_pos = "0 :: 32 word" and q_len = addr_len,
          OF out_addr i_lt j_lt out_no_overflow addr_no_overflow
            out_range addr_range0])
  next
    fix i j
    assume i_lt: "i < unat addr_len"
      and j_lt: "j < unat addr_len"
      and neq: "i \<noteq> j"
    show "out +\<^sub>p uint (pos + of_nat i) \<noteq>
      out +\<^sub>p uint (pos + of_nat j)"
    proof
      assume eq: "out +\<^sub>p uint (pos + of_nat i) =
        out +\<^sub>p uint (pos + of_nat j)"
      have "i = j"
        by (rule ptr_range_distinct_word_range_inj[
            OF out_dist out_no_overflow out_range i_lt j_lt eq])
      thus False using neq by simp
    qed
  next
    fix k i
    assume k_lt: "k < unat pos"
      and i_lt: "i < addr_len"
    show "out +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule ptr_range_distinct_word_prefix_disj[
          OF out_dist out_no_overflow out_range k_lt i_lt])
  next
    show "unat pos + unat addr_len < 2 ^ 32"
      by (rule out_no_overflow)
  next
    fix k i
    assume k_lt: "k < data_n"
      and i_lt: "i < addr_len"
    have data_out: "bufs_disjoint data (unat data_cap) out (unat out_cap)"
      using out_data by (simp add: bufs_disjoint_sym)
    show "data +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF data_out _ i_lt out_no_overflow out_range])
        (use k_lt data_range in simp)
  next
    fix k i
    assume k_lt: "k < inst_n"
      and i_lt: "i < addr_len"
    have inst_out: "bufs_disjoint inst (unat inst_cap) out (unat out_cap)"
      using out_inst by (simp add: bufs_disjoint_sym)
    show "inst +\<^sub>p int k \<noteq> out +\<^sub>p uint (pos + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
          OF inst_out _ i_lt out_no_overflow out_range])
        (use k_lt inst_range in simp)
  qed
qed

definition encoder_index_post ::
  "lifted_globals \<Rightarrow> lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> bool" where
  "encoder_index_post s t src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes \<longleftrightarrow>
     source_index_heap_rel t src_bytes head_arr next_arr \<and>
     source_index_heap_nexts_wf t src_bytes next_arr \<and>
     source_index_heap_chains_closed t src_bytes head_arr next_arr \<and>
     heap_bytes t src (unat src_len) = src_bytes \<and>
     heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
     heap_typing t = heap_typing s"

definition encoder_window_post ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow>
   sections_t_C \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> bool" where
  "encoder_window_post s data inst addr sec src_bytes tgt_bytes \<longleftrightarrow>
     sections_t_C.err_C sec = ENC_OK \<and>
     sections_fit_32 src_bytes tgt_bytes (encode_window_full_spec src_bytes tgt_bytes) \<and>
     emitted_sections s data inst addr sec
       (efr_data (encode_window_full_spec src_bytes tgt_bytes))
       (efr_inst (encode_window_full_spec src_bytes tgt_bytes))
       (efr_addr (encode_window_full_spec src_bytes tgt_bytes))"

definition encoder_window_caps_ok ::
  "sections_t_C \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> bool" where
  "encoder_window_caps_ok sec data_cap inst_cap addr_cap \<longleftrightarrow>
     unat (sections_t_C.data_pos_C sec) \<le> unat data_cap \<and>
     unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap \<and>
     unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"

definition encoder_success_post ::
  "8 word ptr \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> 32 word \<Rightarrow>
   lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "encoder_success_post out src_bytes tgt_bytes n s t \<longleftrightarrow>
     unat n = length (encode_spec src_bytes tgt_bytes) \<and>
     heap_bytes t out (length (encode_spec src_bytes tgt_bytes)) =
       encode_spec src_bytes tgt_bytes \<and>
     heap_typing t = heap_typing s"

lemma encode_spec_fast_path_topdown:
  assumes fit: "sections_fit_32 src tgt (encode_window_full_spec src tgt)"
  shows "encode_spec src tgt =
    serialize src tgt
      (efr_data (encode_window_full_spec src tgt))
      (efr_inst (encode_window_full_spec src tgt))
      (efr_addr (encode_window_full_spec src tgt))"
  using fit by (simp add: encode_spec_alt Let_def)

lemma vcdiff_encode'_build_index_phase_topdown:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
        "encoder_input_rel s src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and src_len_word: "unat src_len < unat (no_entry32 :: 32 word)"
      and head_valid:
        "\<And>h. h < hash_size \<Longrightarrow>
          ptr_valid (heap_typing s) (head_arr +\<^sub>p int h)"
      and next_valid:
        "\<And>p. p < unat src_len \<Longrightarrow>
          ptr_valid (heap_typing s) (next_arr +\<^sub>p int p)"
      and head_no_alias:
        "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
          head_arr +\<^sub>p int h \<noteq> head_arr +\<^sub>p int bucket"
      and next_no_alias:
        "\<And>q p. \<lbrakk>q < unat src_len; p < unat src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      and next_head_disjoint:
        "\<And>h p. \<lbrakk>h < hash_size; p < unat src_len\<rbrakk> \<Longrightarrow>
          head_arr +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
      and head_next_disjoint:
        "\<And>q bucket. \<lbrakk>q < unat src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> head_arr +\<^sub>p int bucket"
  shows "build_index' src src_len head_arr next_arr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               encoder_index_post s t src src_len tgt tgt_len head_arr next_arr
                 src_bytes tgt_bytes \<rbrace>"
proof -
  have src_ok: "buf_valid s src (unat src_len)"
    using buffers by (simp add: encoder_buffers_ok_def)
  have tgt_ok: "buf_valid s tgt (unat tgt_len)"
    using buffers by (simp add: encoder_buffers_ok_def)
  have tp_le: "(0 :: 32 word) \<le> tgt_len"
    by simp
  have raw:
    "build_index' src src_len head_arr next_arr \<bullet> s
      \<lbrace> \<lambda>r t. r = Result () \<and>
          source_index_heap_rel t
            (heap_bytes s src (unat src_len)) head_arr next_arr \<and>
          source_index_heap_nexts_wf t
            (heap_bytes s src (unat src_len)) next_arr \<and>
          source_index_heap_chains_closed t
            (heap_bytes s src (unat src_len)) head_arr next_arr \<and>
          heap_typing t = heap_typing s \<and>
          heap_bytes t src (unat src_len) =
            heap_bytes s src (unat src_len) \<and>
          heap_bytes t tgt (unat tgt_len) =
            heap_bytes s tgt (unat tgt_len) \<and>
          buf_valid t tgt (unat tgt_len) \<and>
          (\<forall>m. find_best_match' src src_len tgt tgt_len (0 :: 32 word) head_arr next_arr t =
                Some m \<longrightarrow>
              (m = (let best = find_best_match_spec
                  (heap_bytes s src (unat src_len))
                  (heap_bytes s tgt (unat tgt_len)) (unat (0 :: 32 word))
                  (build_index_spec (heap_bytes s src (unat src_len)))
                in match_t_C (of_nat (em_pos best)) (of_nat (em_len best)))
              \<and> match_valid
                (heap_bytes s src (unat src_len))
                (heap_bytes s tgt (unat tgt_len))
                (unat (0 :: 32 word)) (unat (match_t_C.pos_C m))
                (unat (match_t_C.len_C m)))) \<rbrace>"
  proof (rule build_index'_find_best_match'_spec_and_valid_preserves_tgt_buf_valid[
      where src = src and tgt = tgt and src_len = src_len
        and tgt_len = tgt_len and tp = "0 :: 32 word" and head = head_arr
        and next_arr = next_arr and s = s])
    show "unat src_len < unat (no_entry32 :: 32 word)"
      by (rule src_len_word)
    show "buf_valid s src (unat src_len)"
      by (rule src_ok)
    show "buf_valid s tgt (unat tgt_len)"
      by (rule tgt_ok)
    show "(0 :: 32 word) \<le> tgt_len"
      by (rule tp_le)
  next
    fix h st'
    assume typing: "heap_typing st' = heap_typing s"
      and h_lt: "h < hash_size"
    have ptr: "ptr_valid (heap_typing s) (head_arr +\<^sub>p int h)"
      by (rule head_valid[OF h_lt])
    show "IS_VALID(32 word) st' (head_arr +\<^sub>p int h)"
      using ptr typing by simp
  next
    fix p st'
    assume typing: "heap_typing st' = heap_typing s"
      and p_lt: "p < unat src_len"
    have ptr: "ptr_valid (heap_typing s) (next_arr +\<^sub>p int p)"
      by (rule next_valid[OF p_lt])
    show "IS_VALID(32 word) st' (next_arr +\<^sub>p int p)"
      using ptr typing by simp
  next
    fix h bucket
    assume h_lt: "h < hash_size"
      and bucket_lt: "bucket < hash_size"
      and neq: "h \<noteq> bucket"
    show "head_arr +\<^sub>p int h \<noteq> head_arr +\<^sub>p int bucket"
      by (rule head_no_alias[where h = h and bucket = bucket,
          OF h_lt bucket_lt neq])
  next
    fix q p
    assume q_lt: "q < unat src_len"
      and p_lt: "p < unat src_len"
      and neq: "q \<noteq> p"
    show "next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      by (rule next_no_alias[where q = q and p = p, OF q_lt p_lt neq])
  next
    fix h p
    assume h_lt: "h < hash_size"
      and p_lt: "p < unat src_len"
    show "head_arr +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
      by (rule next_head_disjoint[where h = h and p = p, OF h_lt p_lt])
  next
    fix q bucket
    assume q_lt: "q < unat src_len"
      and bucket_lt: "bucket < hash_size"
    show "next_arr +\<^sub>p int q \<noteq> head_arr +\<^sub>p int bucket"
      by (rule head_next_disjoint[where q = q and bucket = bucket,
          OF q_lt bucket_lt])
  qed
  show ?thesis
    apply (rule runs_to_weaken[OF raw])
    using input
    apply (auto simp: encoder_input_rel_def encoder_index_post_def)
    done
qed

definition encode_window_final_spec_state ::
  "byte list \<Rightarrow> byte list \<Rightarrow> enc_full_state" where
  "encode_window_final_spec_state src_bytes tgt_bytes =
     encode_window_full_loop (length tgt_bytes + 1) src_bytes tgt_bytes
       (build_index_spec src_bytes) enc_full_init"

definition encode_window_loop_buffers_ok ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> bool" where
  "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap \<longleftrightarrow>
     buf_valid s src (unat src_len) \<and>
     buf_valid s tgt (unat tgt_len) \<and>
     buf_valid s pending (unat pending_cap) \<and>
     buf_valid s data (unat data_cap) \<and>
     buf_valid s inst (unat inst_cap) \<and>
     buf_valid s addr (unat addr_cap) \<and>
     ptr_range_distinct src (unat src_len) \<and>
     ptr_range_distinct tgt (unat tgt_len) \<and>
     ptr_range_distinct pending (unat pending_cap) \<and>
     ptr_range_distinct data (unat data_cap) \<and>
     ptr_range_distinct inst (unat inst_cap) \<and>
     ptr_range_distinct addr (unat addr_cap) \<and>
     unat tgt_len \<le> unat pending_cap \<and>
     unat tgt_len + 64 \<le> unat data_cap \<and>
     unat tgt_len + 64 \<le> unat inst_cap \<and>
     unat tgt_len + 64 \<le> unat addr_cap \<and>
     bufs_disjoint pending (unat pending_cap) src (unat src_len) \<and>
     bufs_disjoint pending (unat pending_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint pending (unat pending_cap) data (unat data_cap) \<and>
     bufs_disjoint pending (unat pending_cap) inst (unat inst_cap) \<and>
     bufs_disjoint pending (unat pending_cap) addr (unat addr_cap) \<and>
     bufs_disjoint data (unat data_cap) src (unat src_len) \<and>
     bufs_disjoint data (unat data_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint data (unat data_cap) inst (unat inst_cap) \<and>
     bufs_disjoint data (unat data_cap) addr (unat addr_cap) \<and>
     bufs_disjoint inst (unat inst_cap) src (unat src_len) \<and>
     bufs_disjoint inst (unat inst_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint inst (unat inst_cap) addr (unat addr_cap) \<and>
     bufs_disjoint addr (unat addr_cap) src (unat src_len) \<and>
     bufs_disjoint addr (unat addr_cap) tgt (unat tgt_len)"

lemma encoder_buffers_ok_encode_window_loop_buffers_ok:
  assumes buffers:
    "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
  shows "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
  using buffers
  by (simp add: encoder_buffers_ok_def encode_window_loop_buffers_ok_def)

definition encode_window_match_rel ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> bool" where
  "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes \<longleftrightarrow>
     (\<forall>tp m. tp \<le> tgt_len \<longrightarrow>
        find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
          Some m \<longrightarrow>
        m = (let best =
               find_best_match_spec src_bytes tgt_bytes (unat tp)
                 (build_index_spec src_bytes)
             in match_t_C (of_nat (em_pos best)) (of_nat (em_len best))) \<and>
        match_valid src_bytes tgt_bytes (unat tp)
          (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)))"

definition encode_window_loop_rel ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   sections_t_C \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> enc_full_state \<Rightarrow> bool" where
  "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st \<longleftrightarrow>
     heap_bytes s src (unat src_len) = src_bytes \<and>
     heap_bytes s tgt (unat tgt_len) = tgt_bytes \<and>
     length src_bytes = unat src_len \<and>
     length tgt_bytes = unat tgt_len \<and>
     heap_bytes_word s pending (0 :: 32 word) pend_len =
       enc_pending spec_st \<and>
     length (enc_pending spec_st) = unat pend_len \<and>
     enc_tp spec_st = unat tp \<and>
     enc_flushed spec_st + length (enc_pending spec_st) = enc_tp spec_st \<and>
     enc_sections_state_rel s data inst addr sec spec_st \<and>
     sections_t_C.err_C sec = ENC_OK \<and>
     unat pend_len \<le> unat pending_cap \<and>
     unat (sections_t_C.data_pos_C sec) \<le> unat data_cap \<and>
     unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap \<and>
     unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"

definition encode_window_c_loop_body ::
  "8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word \<times> sections_t_C \<times> 32 word \<Rightarrow>
   (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
    lifted_globals) exn_monad" where
  "encode_window_c_loop_body
     src src_len tgt tgt_len head_arr next_arr
     data data_cap inst inst_cap addr addr_cap pending pending_cap =
   (\<lambda>(pend_len, sec, tp). do {
      m \<leftarrow> gets_the
            (find_best_match' src src_len tgt tgt_len tp head_arr next_arr);
      condition (\<lambda>s. match_t_C.len_C m < 4)
        (condition (\<lambda>s. pending_cap \<le> pend_len)
           (throw (sections_t_C.err_C_update (\<lambda>_. 1) sec))
           (liftE (do {
              guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
              guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
              modify
                (heap_w8_update
                  (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                         h (tgt +\<^sub>p uint tp))));
              return (pend_len + 1, sec, tp + 1)
            })))
        (do {
           here \<leftarrow> return (src_len + tp);
           f \<leftarrow> liftE
                (try_emit_add_copy' sec data data_cap inst inst_cap
                  addr addr_cap pending pend_len
                  (match_t_C.pos_C m) here (match_t_C.len_C m));
           unless (sections_t_C.err_C (fused_t_C.s_C f) = 0)
            (throw (fused_t_C.s_C f));
           condition (\<lambda>s. fused_t_C.fused_C f \<noteq> 0)
             (do {
                consumed \<leftarrow> return (fused_t_C.fused_C f);
                sec \<leftarrow> return (fused_t_C.s_C f);
                tp \<leftarrow> return (tp + consumed);
                (sec, tp) \<leftarrow>
                  condition (\<lambda>s. consumed < match_t_C.len_C m)
                    (do {
                       rem \<leftarrow> return (match_t_C.len_C m - consumed);
                       sec \<leftarrow> liftE
                         (emit_copy' sec inst inst_cap addr addr_cap
                           (match_t_C.pos_C m + consumed)
                           (src_len + tp) rem);
                       unless (sections_t_C.err_C sec = 0) (throw sec);
                       return (sec, tp + rem)
                     })
                    (return (sec, tp));
                return (0, sec, tp)
              })
             (do {
                (pend_len, sec, tp) \<leftarrow> return (pend_len, sec, tp);
                (pend_len, sec) \<leftarrow>
                  condition (\<lambda>s. 0 < pend_len)
                    (do {
                       sec \<leftarrow> liftE
                         (flush_pending' sec data data_cap inst inst_cap
                           pending pend_len);
                       unless (sections_t_C.err_C sec = 0) (throw sec);
                       return (0, sec)
                     })
                    (return (pend_len, sec));
                sec \<leftarrow> liftE
                  (emit_copy' sec inst inst_cap addr addr_cap
                    (match_t_C.pos_C m) here (match_t_C.len_C m));
                unless (sections_t_C.err_C sec = 0) (throw sec);
                return (pend_len, sec, tp + match_t_C.len_C m)
              })
         })
    })"

lemma encoder_index_post_encode_window_match_rel:
  assumes buffers:
    "encoder_buffers_ok s0 out out_cap src src_len tgt tgt_len head_arr next_arr
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and index:
    "encoder_index_post s0 s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
  shows "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
  sorry

lemma encode_window_initial_loop_rel:
  assumes input:
    "encoder_input_rel s0 src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and sec_zero:
    "sections_t_C.data_pos_C sec = 0"
    "sections_t_C.inst_pos_C sec = 0"
    "sections_t_C.addr_pos_C sec = 0"
    "sections_t_C.err_C sec = ENC_OK"
      and bytes:
    "heap_bytes s src (unat src_len) = src_bytes"
    "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
    "length src_bytes = unat src_len"
    "length tgt_bytes = unat tgt_len"
  shows "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec 0 0 src_bytes tgt_bytes enc_full_init"
  sorry

lemma encode_window_pending_byte_step_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and tp_lt: "tp < tgt_len"
      and short: "match_t_C.len_C m < (of_nat min_match :: 32 word)"
      and match:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
  shows "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            (pend_len, sec, tp) \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
              r = Result (pend_len', sec', tp') \<and>
              spec_st' = buffer_pending_byte_spec (tgt_bytes ! unat tp)
                spec_st \<and>
              encode_window_loop_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp) \<rbrace>"
  sorry

lemma encode_window_try_fused_copy_step_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and match_len: "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
      and fused:
    "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st =
      Some spec_st'"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
            pending pend_len (match_t_C.pos_C m) (src_len + tp)
            (match_t_C.len_C m) \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>f.
              r = Result f \<and>
              fused_t_C.fused_C f \<noteq> 0 \<and>
              sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK \<and>
              enc_sections_state_rel t data inst addr (fused_t_C.s_C f)
                spec_st' \<and>
              heap_bytes t src (unat src_len) = src_bytes \<and>
              heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
              heap_typing t = heap_typing s \<rbrace>"
  sorry

lemma encode_window_flush_then_copy_step_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and match_len: "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
      and fused_none:
    "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st =
      None"
  shows "(do {
            (pend_len, sec) \<leftarrow>
              condition (\<lambda>s. 0 < pend_len)
                (do {
                   sec \<leftarrow> liftE
                     (flush_pending' sec data data_cap inst inst_cap
                       pending pend_len);
                   unless (sections_t_C.err_C sec = 0) (throw sec);
                   return (0, sec)
                 })
                (return (pend_len, sec));
            sec \<leftarrow> liftE
              (emit_copy' sec inst inst_cap addr addr_cap
                (match_t_C.pos_C m) (src_len + tp) (match_t_C.len_C m));
            unless (sections_t_C.err_C sec = 0) (throw sec);
            return (pend_len, sec, tp + match_t_C.len_C m)
          } :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
              r = Result (pend_len', sec', tp') \<and>
              spec_st' = flush_then_emit_copy_spec (length src_bytes)
                (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))
                spec_st \<and>
              encode_window_loop_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
              heap_typing t = heap_typing s \<rbrace>"
  sorry

lemma encode_window_match_step_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and tp_lt: "tp < tgt_len"
      and match:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
      and match_len: "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
  shows "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            (pend_len, sec, tp) \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
              r = Result (pend_len', sec', tp') \<and>
              encode_window_loop_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
              enc_tp spec_st < enc_tp spec_st' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp) \<rbrace>"
proof -
  have fused_case:
    "\<And>spec_st'. try_emit_add_copy_spec (length src_bytes)
        (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st =
        Some spec_st' \<Longrightarrow>
      try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
        pending pend_len (match_t_C.pos_C m) (src_len + tp)
        (match_t_C.len_C m) \<bullet> s
      \<lbrace> \<lambda>r t. \<exists>f.
          r = Result f \<and>
          fused_t_C.fused_C f \<noteq> 0 \<and>
          sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK \<and>
          enc_sections_state_rel t data inst addr (fused_t_C.s_C f)
            spec_st' \<and>
          heap_bytes t src (unat src_len) = src_bytes \<and>
          heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule encode_window_try_fused_copy_step_topdown[OF rel match_len])
  have fallback_case:
    "try_emit_add_copy_spec (length src_bytes)
        (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st =
        None \<Longrightarrow>
      (do {
        (pend_len, sec) \<leftarrow>
          condition (\<lambda>s. 0 < pend_len)
            (do {
               sec \<leftarrow> liftE
                 (flush_pending' sec data data_cap inst inst_cap
                   pending pend_len);
               unless (sections_t_C.err_C sec = 0) (throw sec);
               return (0, sec)
             })
            (return (pend_len, sec));
        sec \<leftarrow> liftE
          (emit_copy' sec inst inst_cap addr addr_cap
            (match_t_C.pos_C m) (src_len + tp) (match_t_C.len_C m));
        unless (sections_t_C.err_C sec = 0) (throw sec);
        return (pend_len, sec, tp + match_t_C.len_C m)
      } :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
            lifted_globals) exn_monad) \<bullet> s
      \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
          r = Result (pend_len', sec', tp') \<and>
          spec_st' = flush_then_emit_copy_spec (length src_bytes)
            (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))
            spec_st \<and>
          encode_window_loop_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule encode_window_flush_then_copy_step_topdown[OF rel match_len])
  show ?thesis
  sorry
qed

lemma encode_window_loop_body_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and tp_lt: "tp < tgt_len"
  shows "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            (pend_len, sec, tp) \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
              r = Result (pend_len', sec', tp') \<and>
              encode_window_loop_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
              enc_tp spec_st < enc_tp spec_st' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp) \<rbrace>"
proof -
  have pending_case:
    "\<And>m. \<lbrakk>
      match_t_C.len_C m < (of_nat min_match :: 32 word);
      find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
        Some m
    \<rbrakk> \<Longrightarrow>
      encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> s
      \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
          r = Result (pend_len', sec', tp') \<and>
          spec_st' = buffer_pending_byte_spec (tgt_bytes ! unat tp)
            spec_st \<and>
          encode_window_loop_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
          (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp) \<rbrace>"
    by (rule encode_window_pending_byte_step_topdown[OF rel tp_lt])
  have match_case:
    "\<And>m. \<lbrakk>
      find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
        Some m;
      (of_nat min_match :: 32 word) \<le> match_t_C.len_C m
    \<rbrakk> \<Longrightarrow>
      encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> s
      \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
          r = Result (pend_len', sec', tp') \<and>
          encode_window_loop_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
          enc_tp spec_st < enc_tp spec_st' \<and>
          (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp) \<rbrace>"
    by (rule encode_window_match_step_topdown[OF rel match_rel tp_lt])
  show ?thesis
  sorry
qed

lemma encode_window_while_loop_topdown:
  fixes src tgt data inst addr pending :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
    "encoder_input_rel s0 src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
    "encoder_buffers_ok s0 out out_cap src src_len tgt tgt_len head_arr next_arr
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and index:
    "encoder_index_post s0 s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and fit:
    "sections_fit_32 src_bytes tgt_bytes
      (encode_window_full_spec src_bytes tgt_bytes)"
      and init:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec0 0 0 src_bytes tgt_bytes enc_full_init"
  shows "(whileLoop (\<lambda>(pend_len, sec, tp) s. tp < tgt_len)
           (encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
             data data_cap inst inst_cap addr addr_cap pending pending_cap)
           (0, sec0, 0) ::
          (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
           lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>pend_len sec tp spec_st.
              r = Result (pend_len, sec, tp) \<and>
              \<not> tp < tgt_len \<and>
              encode_window_loop_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec tp pend_len src_bytes tgt_bytes spec_st \<and>
              flush_pending_spec (length src_bytes) spec_st =
                encode_window_final_spec_state src_bytes tgt_bytes \<rbrace>"
proof -
  have match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
    by (rule encoder_index_post_encode_window_match_rel[OF buffers index])
  have loop_buffers0:
    "encode_window_loop_buffers_ok s0 src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    by (rule encoder_buffers_ok_encode_window_loop_buffers_ok[OF buffers])
  have body_progress:
    "\<And>sec tp pend_len spec_st. \<lbrakk>
      encode_window_loop_rel s src src_len tgt tgt_len
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        sec tp pend_len src_bytes tgt_bytes spec_st;
      tp < tgt_len
    \<rbrakk> \<Longrightarrow>
      encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> s
      \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
          r = Result (pend_len', sec', tp') \<and>
          encode_window_loop_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
          enc_tp spec_st < enc_tp spec_st' \<and>
          (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp) \<rbrace>"
    by (rule encode_window_loop_body_topdown[OF _ match_rel])
  show ?thesis
  sorry
qed

lemma encode_window_final_flush_topdown:
  fixes src tgt data inst addr pending :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
    "encoder_input_rel s0 src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
    "encoder_buffers_ok s0 out out_cap src src_len tgt tgt_len head_arr next_arr
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and index:
    "encoder_index_post s0 s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and fit:
    "sections_fit_32 src_bytes tgt_bytes
      (encode_window_full_spec src_bytes tgt_bytes)"
      and loop_exit:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and exit: "\<not> tp < tgt_len"
      and final_spec:
    "flush_pending_spec (length src_bytes) spec_st =
      encode_window_final_spec_state src_bytes tgt_bytes"
  shows "((liftE
            (condition (\<lambda>s. 0 < pend_len)
              (flush_pending' sec data data_cap inst inst_cap pending pend_len)
              (return sec)) >>= throw) ::
          (sections_t_C, sections_t_C, lifted_globals) exn_monad) \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec'.
              r = Result sec' \<and>
              enc_sections_state_rel t data inst addr sec'
                (encode_window_final_spec_state src_bytes tgt_bytes) \<and>
              sections_t_C.err_C sec' = ENC_OK \<and>
              encoder_window_caps_ok sec' data_cap inst_cap addr_cap \<and>
              heap_bytes t src (unat src_len) = src_bytes \<and>
              heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have pending_eq:
    "enc_pending spec_st = heap_bytes_word s pending 0 pend_len"
    using loop_exit by (simp add: encode_window_loop_rel_def)
  have rel:
    "enc_sections_state_rel s data inst addr sec spec_st"
    using loop_exit by (simp add: encode_window_loop_rel_def)
  show ?thesis
  sorry
qed

lemma encode_window_phase_core_topdown:
  fixes src tgt data inst addr pending :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
        "encoder_input_rel s0 src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_ok s0 out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and index:
        "encoder_index_post s0 s src src_len tgt tgt_len head_arr next_arr
          src_bytes tgt_bytes"
      and fit:
        "sections_fit_32 src_bytes tgt_bytes
          (encode_window_full_spec src_bytes tgt_bytes)"
  shows "encode_window' src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>sec spec_st.
               r = Result sec \<and>
               spec_st = encode_window_final_spec_state src_bytes tgt_bytes \<and>
               enc_sections_state_rel t data inst addr sec spec_st \<and>
               sections_t_C.err_C sec = ENC_OK \<and>
               encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
               heap_bytes t src (unat src_len) = src_bytes \<and>
               heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
               heap_typing t = heap_typing s \<rbrace>"
proof -
  have match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
    by (rule encoder_index_post_encode_window_match_rel[OF buffers index])
  have loop_buffers0:
    "encode_window_loop_buffers_ok s0 src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    by (rule encoder_buffers_ok_encode_window_loop_buffers_ok[OF buffers])
  show ?thesis
  sorry
qed

lemma vcdiff_encode'_encode_window_phase_topdown:
  fixes src tgt data inst addr pending :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
        "encoder_input_rel s0 src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_ok s0 out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and index:
        "encoder_index_post s0 s src src_len tgt tgt_len head_arr next_arr
          src_bytes tgt_bytes"
      and fit:
        "sections_fit_32 src_bytes tgt_bytes
          (encode_window_full_spec src_bytes tgt_bytes)"
  shows "encode_window' src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>sec.
               r = Result sec \<and>
               encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
               encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
               heap_bytes t src (unat src_len) = src_bytes \<and>
               heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
               heap_typing t = heap_typing s \<rbrace>"
proof (rule runs_to_weaken[
    OF encode_window_phase_core_topdown[
      OF input buffers index fit]])
  fix r t
  assume post:
    "\<exists>sec spec_st.
      r = Result sec \<and>
      spec_st = encode_window_final_spec_state src_bytes tgt_bytes \<and>
      enc_sections_state_rel t data inst addr sec spec_st \<and>
      sections_t_C.err_C sec = ENC_OK \<and>
      encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
      heap_bytes t src (unat src_len) = src_bytes \<and>
      heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
      heap_typing t = heap_typing s"
  then obtain sec spec_st where
      r_def: "r = Result sec"
    and spec_st:
      "spec_st = encode_window_final_spec_state src_bytes tgt_bytes"
    and rel: "enc_sections_state_rel t data inst addr sec spec_st"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and caps: "encoder_window_caps_ok sec data_cap inst_cap addr_cap"
    and src_heap: "heap_bytes t src (unat src_len) = src_bytes"
    and tgt_heap: "heap_bytes t tgt (unat tgt_len) = tgt_bytes"
    and typing: "heap_typing t = heap_typing s"
    by blast
  have emitted:
    "emitted_sections t data inst addr sec
      (efr_data (encode_window_full_spec src_bytes tgt_bytes))
      (efr_inst (encode_window_full_spec src_bytes tgt_bytes))
      (efr_addr (encode_window_full_spec src_bytes tgt_bytes))"
    using rel spec_st
    by (simp add: enc_sections_state_rel_def
      encode_window_final_spec_state_def encode_window_full_spec_def
      enc_full_result_of_state_def Let_def)
  show "\<exists>sec.
      r = Result sec \<and>
      encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
      encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
      heap_bytes t src (unat src_len) = src_bytes \<and>
      heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
      heap_typing t = heap_typing s"
    using r_def fit sec_ok emitted caps src_heap tgt_heap typing
    by (auto simp: encoder_window_post_def)
qed

lemma vcdiff_encode'_serialize_phase_topdown:
  fixes out data inst addr :: "8 word ptr"
    and out_cap src_len tgt_len :: "32 word"
  assumes input:
        "encoder_input_rel s0 src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_ok s0 out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and fit:
        "sections_fit_32 src_bytes tgt_bytes
          (encode_window_full_spec src_bytes tgt_bytes)"
      and out_cap_ok:
        "length (encode_spec src_bytes tgt_bytes) \<le> unat out_cap"
      and encoded_len_word:
        "length (encode_spec src_bytes tgt_bytes) < 2 ^ 32"
      and typing: "heap_typing s = heap_typing s0"
      and window:
        "encoder_window_post s data inst addr sec src_bytes tgt_bytes"
      and window_caps:
        "encoder_window_caps_ok sec data_cap inst_cap addr_cap"
  shows "serialize' out out_cap src_len tgt_len
            data (sections_t_C.data_pos_C sec)
            inst (sections_t_C.inst_pos_C sec)
            addr (sections_t_C.addr_pos_C sec) \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>n.
               r = Result n \<and>
               encoder_success_post out src_bytes tgt_bytes n s t \<rbrace>"
proof -
  let ?r = "encode_window_full_spec src_bytes tgt_bytes"
  let ?data_bytes = "efr_data ?r"
  let ?inst_bytes = "efr_inst ?r"
  let ?addr_bytes = "efr_addr ?r"
  let ?data_len = "sections_t_C.data_pos_C sec"
  let ?inst_len = "sections_t_C.inst_pos_C sec"
  let ?addr_len = "sections_t_C.addr_pos_C sec"
  have buffers_s:
    "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    by (rule encoder_buffers_ok_heap_typing_eq[OF typing buffers])
  have input_len:
    "unat src_len = length src_bytes"
    "unat tgt_len = length tgt_bytes"
    using input by (simp_all add: encoder_input_rel_def)
  have window_parts:
    "sections_t_C.err_C sec = ENC_OK"
    "sections_fit_32 src_bytes tgt_bytes ?r"
    "emitted_sections s data inst addr sec ?data_bytes ?inst_bytes ?addr_bytes"
    using window by (simp_all add: encoder_window_post_def)
  have emitted_heaps:
    "heap_bytes s data (unat ?data_len) = ?data_bytes"
    "heap_bytes s inst (unat ?inst_len) = ?inst_bytes"
    "heap_bytes s addr (unat ?addr_len) = ?addr_bytes"
    using emitted_sectionsD[OF window_parts(3)] by simp_all
  have data_len: "unat ?data_len = length ?data_bytes"
    using emitted_heaps(1) by (metis heap_bytes_length)
  have inst_len: "unat ?inst_len = length ?inst_bytes"
    using emitted_heaps(2) by (metis heap_bytes_length)
  have addr_len: "unat ?addr_len = length ?addr_bytes"
    using emitted_heaps(3) by (metis heap_bytes_length)
  have data_len_rev: "length ?data_bytes = unat ?data_len"
    using data_len by simp
  have inst_len_rev: "length ?inst_bytes = unat ?inst_len"
    using inst_len by simp
  have addr_len_rev: "length ?addr_bytes = unat ?addr_len"
    using addr_len by simp
  have data_heap: "heap_bytes s data (length ?data_bytes) = ?data_bytes"
    and inst_heap: "heap_bytes s inst (length ?inst_bytes) = ?inst_bytes"
    and addr_heap: "heap_bytes s addr (length ?addr_bytes) = ?addr_bytes"
    using emitted_heaps data_len inst_len addr_len by simp_all
  have section_caps:
    "length ?data_bytes \<le> unat data_cap"
    "length ?inst_bytes \<le> unat inst_cap"
    "length ?addr_bytes \<le> unat addr_cap"
    using window_caps data_len inst_len addr_len
    by (simp_all add: encoder_window_caps_ok_def)
  obtain src_n where src_size: "varint_size' src_len s = Some src_n"
    using varint_size'_some by blast
  obtain tgt_n where tgt_size: "varint_size' tgt_len s = Some tgt_n"
    using varint_size'_some by blast
  obtain data_n where data_size: "varint_size' ?data_len s = Some data_n"
    using varint_size'_some by blast
  obtain inst_n where inst_size: "varint_size' ?inst_len s = Some inst_n"
    using varint_size'_some by blast
  obtain addr_n where addr_size: "varint_size' ?addr_len s = Some addr_n"
    using varint_size'_some by blast
  let ?dlen_nat =
    "varint_size (length tgt_bytes) + 1 +
     varint_size (length ?data_bytes) +
     varint_size (length ?inst_bytes) +
     varint_size (length ?addr_bytes) +
     length ?data_bytes + length ?inst_bytes + length ?addr_bytes"
  let ?dlen =
    "tgt_n + 1 + data_n + inst_n + addr_n +
     ?data_len + ?inst_len + ?addr_len"
  have size_unats:
    "unat tgt_n = varint_size (length tgt_bytes)"
    "unat data_n = varint_size (length ?data_bytes)"
    "unat inst_n = varint_size (length ?inst_bytes)"
    "unat addr_n = varint_size (length ?addr_bytes)"
    using varint_size'_unat_eq_varint_size[OF tgt_size]
          varint_size'_unat_eq_varint_size[OF data_size]
          varint_size'_unat_eq_varint_size[OF inst_size]
          varint_size'_unat_eq_varint_size[OF addr_size]
	          input_len data_len inst_len addr_len
	    by simp_all
  have src_size_unat:
    "src_bytes \<noteq> [] \<Longrightarrow> unat src_n = varint_size (length src_bytes)"
    using varint_size'_unat_eq_varint_size[OF src_size] input_len by simp
  have size_le5:
    "unat src_n \<le> 5"
    "unat tgt_n \<le> 5"
    "unat data_n \<le> 5"
    "unat inst_n \<le> 5"
    "unat addr_n \<le> 5"
    using varint_size'_le5[OF src_size]
          varint_size'_le5[OF tgt_size]
          varint_size'_le5[OF data_size]
          varint_size'_le5[OF inst_size]
          varint_size'_le5[OF addr_size]
    by simp_all
  have dlen_bound: "?dlen_nat < 2 ^ 32"
    using window_parts(2) by (simp add: sections_fit_32_def)
  have dlen_unat: "unat ?dlen = ?dlen_nat"
  proof -
    let ?w1 = "tgt_n + (1 :: 32 word)"
    let ?w2 = "?w1 + data_n"
    let ?w3 = "?w2 + inst_n"
    let ?w4 = "?w3 + addr_n"
    let ?w5 = "?w4 + ?data_len"
    let ?w6 = "?w5 + ?inst_len"
    have total:
      "unat tgt_n + 1 + unat data_n + unat inst_n + unat addr_n +
       unat ?data_len + unat ?inst_len + unat ?addr_len < 2 ^ 32"
      using dlen_bound size_unats data_len inst_len addr_len by simp
    have w1_no_overflow: "unat tgt_n + unat (1 :: 32 word) < 2 ^ 32"
      using total by simp
    have w1_raw: "unat ?w1 = unat tgt_n + unat (1 :: 32 word)"
      by (rule unat_word_add_no_overflow[
          where a = tgt_n and b = "1 :: 32 word"])
        (rule w1_no_overflow)
    have w1: "unat ?w1 = unat tgt_n + 1"
      using w1_raw by simp
    have w2_add: "unat (?w1 + data_n) = unat ?w1 + unat data_n"
      by (rule unat_word_add_no_overflow) (use total w1 in linarith)
    have w2: "unat ?w2 = unat tgt_n + 1 + unat data_n"
      using w1 w2_add by simp
    have w3_add: "unat (?w2 + inst_n) = unat ?w2 + unat inst_n"
      by (rule unat_word_add_no_overflow) (use total w2 in linarith)
    have w3: "unat ?w3 = unat tgt_n + 1 + unat data_n + unat inst_n"
      using w2 w3_add by simp
    have w4_add: "unat (?w3 + addr_n) = unat ?w3 + unat addr_n"
      by (rule unat_word_add_no_overflow) (use total w3 in linarith)
    have w4: "unat ?w4 =
        unat tgt_n + 1 + unat data_n + unat inst_n + unat addr_n"
      using w3 w4_add by simp
    have w5_add: "unat (?w4 + ?data_len) = unat ?w4 + unat ?data_len"
      by (rule unat_word_add_no_overflow) (use total w4 in linarith)
    have w5: "unat ?w5 =
        unat tgt_n + 1 + unat data_n + unat inst_n + unat addr_n +
        unat ?data_len"
      using w4 w5_add by simp
    have w6_add: "unat (?w5 + ?inst_len) = unat ?w5 + unat ?inst_len"
      by (rule unat_word_add_no_overflow) (use total w5 in linarith)
    have w6: "unat ?w6 =
        unat tgt_n + 1 + unat data_n + unat inst_n + unat addr_n +
        unat ?data_len + unat ?inst_len"
      using w5 w6_add by simp
    have w7_add: "unat (?w6 + ?addr_len) = unat ?w6 + unat ?addr_len"
      by (rule unat_word_add_no_overflow) (use total w6 in linarith)
    have "unat (?w6 + ?addr_len) =
        unat tgt_n + 1 + unat data_n + unat inst_n + unat addr_n +
        unat ?data_len + unat ?inst_len + unat ?addr_len"
      using w6 w7_add by simp
    thus ?thesis
      using size_unats data_len inst_len addr_len by simp
  qed
  obtain dlen_n where dlen_size: "varint_size' ?dlen s = Some dlen_n"
    using varint_size'_some by blast
  have dlen_size_unat: "unat dlen_n = varint_size ?dlen_nat"
    using varint_size'_unat_eq_varint_size[OF dlen_size] dlen_unat by simp
  have dlen_size_le5: "unat dlen_n \<le> 5"
    by (rule varint_size'_le5[OF dlen_size])
  have dlen_bytes:
    "varint_bytes32 ?dlen dlen_n = varint_encode ?dlen_nat"
    using varint_bytes32_eq_varint_encode[OF dlen_size] dlen_unat by simp
  have src_bytes:
    "src_bytes \<noteq> [] \<Longrightarrow>
      varint_bytes32 src_len src_n = varint_encode (length src_bytes)"
    using varint_bytes32_eq_varint_encode[OF src_size] input_len by simp
  have tgt_bytes:
    "varint_bytes32 tgt_len tgt_n = varint_encode (length tgt_bytes)"
    using varint_bytes32_eq_varint_encode[OF tgt_size] input_len by simp
  have data_bytes:
    "varint_bytes32 ?data_len data_n = varint_encode (length ?data_bytes)"
    using varint_bytes32_eq_varint_encode[OF data_size] data_len by simp
  have inst_bytes:
    "varint_bytes32 ?inst_len inst_n = varint_encode (length ?inst_bytes)"
    using varint_bytes32_eq_varint_encode[OF inst_size] inst_len by simp
  have addr_bytes:
    "varint_bytes32 ?addr_len addr_n = varint_encode (length ?addr_bytes)"
    using varint_bytes32_eq_varint_encode[OF addr_size] addr_len by simp
  have spec_eq:
    "encode_spec src_bytes tgt_bytes =
      serialize src_bytes tgt_bytes ?data_bytes ?inst_bytes ?addr_bytes"
    by (rule encode_spec_fast_path_topdown[OF window_parts(2)])
  have byte_step:
    "\<And>pos data_n' inst_n' addr_n'. \<lbrakk>
       unat pos < unat out_cap;
       data_n' \<le> unat data_cap;
       inst_n' \<le> unat inst_cap;
       addr_n' \<le> unat addr_cap
     \<rbrakk> \<Longrightarrow>
      serialize_byte_step_ok s out out_cap pos data data_n'
        inst inst_n' addr addr_n'"
    by (rule serialize_byte_step_ok_from_encoder_buffers[OF buffers_s]; assumption)
  have varint_step:
    "\<And>pos v n data_n' inst_n' addr_n'. \<lbrakk>
       varint_size' v s = Some n;
       unat pos + unat n \<le> unat out_cap;
       data_n' \<le> unat data_cap;
       inst_n' \<le> unat inst_cap;
       addr_n' \<le> unat addr_cap
     \<rbrakk> \<Longrightarrow>
      serialize_varint_step_ok s out out_cap pos v n data data_n'
        inst inst_n' addr addr_n'"
    by (rule serialize_varint_step_ok_from_encoder_buffers[OF buffers_s]; assumption)
  have data_copy_step:
    "\<And>pos inst_n' addr_n'. \<lbrakk>
       unat pos + unat ?data_len \<le> unat out_cap;
       unat ?data_len \<le> unat data_cap;
       inst_n' \<le> unat inst_cap;
       addr_n' \<le> unat addr_cap
     \<rbrakk> \<Longrightarrow>
      serialize_copy_step_ok s out out_cap pos data ?data_len
        inst inst_n' addr addr_n'"
    by (rule serialize_data_copy_step_ok_from_encoder_buffers[OF buffers_s]; assumption)
  have inst_copy_step:
    "\<And>pos data_n' addr_n'. \<lbrakk>
       unat pos + unat ?inst_len \<le> unat out_cap;
       unat ?inst_len \<le> unat inst_cap;
       data_n' \<le> unat data_cap;
       addr_n' \<le> unat addr_cap
     \<rbrakk> \<Longrightarrow>
      serialize_copy_step_ok s out out_cap pos inst ?inst_len
        data data_n' addr addr_n'"
    by (rule serialize_inst_copy_step_ok_from_encoder_buffers[OF buffers_s]; assumption)
  have addr_copy_step:
    "\<And>pos data_n' inst_n'. \<lbrakk>
       unat pos + unat ?addr_len \<le> unat out_cap;
       unat ?addr_len \<le> unat addr_cap;
       data_n' \<le> unat data_cap;
       inst_n' \<le> unat inst_cap
     \<rbrakk> \<Longrightarrow>
      serialize_copy_step_ok s out out_cap pos addr ?addr_len
        data data_n' inst inst_n'"
    by (rule serialize_addr_copy_step_ok_from_encoder_buffers[OF buffers_s]; assumption)
  have src_pos_range:
    "unat ((6 :: 32 word) + src_n) + unat (1 :: 32 word) \<le> unat out_cap"
  proof (cases "src_bytes = []")
    case True
    have src_len0: "src_len = 0"
      using input_len(1) True by (simp add: unat_eq_0)
    have src_n1: "src_n = 1"
      using src_size src_len0 by simp
    have pos_unat_raw:
      "unat ((6 :: 32 word) + src_n) = unat (6 :: 32 word) + unat src_n"
      by (rule unat_word_add_no_overflow)
        (use size_le5(1) in simp)
    have pos_unat: "unat ((6 :: 32 word) + src_n) = 6 + unat src_n"
      using pos_unat_raw by simp
    have min_len: "8 \<le> length (encode_spec src_bytes tgt_bytes)"
      using spec_eq True by (simp add: serialize_def Let_def magic_bytes_def)
    show ?thesis
      using out_cap_ok min_len pos_unat src_n1 by simp
  next
    case False
    have pos_unat_raw:
      "unat ((6 :: 32 word) + src_n) = unat (6 :: 32 word) + unat src_n"
      by (rule unat_word_add_no_overflow)
        (use size_le5(1) in simp)
    have pos_unat: "unat ((6 :: 32 word) + src_n) = 6 + unat src_n"
      using pos_unat_raw by simp
    show ?thesis
      using out_cap_ok spec_eq src_size_unat[OF False] pos_unat False
      by (simp add: serialize_def Let_def magic_bytes_def)
  qed
  have src_pos_step:
    "\<And>data_n' inst_n' addr_n'. \<lbrakk>
       data_n' \<le> unat data_cap;
       inst_n' \<le> unat inst_cap;
       addr_n' \<le> unat addr_cap
     \<rbrakk> \<Longrightarrow>
      serialize_varint_step_ok s out out_cap ((6 :: 32 word) + src_n)
        0 1 data data_n' inst inst_n' addr addr_n'"
  proof -
    fix data_n' inst_n' addr_n'
    assume data_cap': "data_n' \<le> unat data_cap"
      and inst_cap': "inst_n' \<le> unat inst_cap"
      and addr_cap': "addr_n' \<le> unat addr_cap"
    have range:
      "unat ((6 :: 32 word) + src_n) + unat (1 :: 32 word) \<le> unat out_cap"
      by (rule src_pos_range)
    have range_suc: "Suc (unat ((6 :: 32 word) + src_n)) \<le> unat out_cap"
      using range by simp
    show "serialize_varint_step_ok s out out_cap ((6 :: 32 word) + src_n)
        0 1 data data_n' inst inst_n' addr addr_n'"
      by (rule varint_step)
        (simp_all add: range range_suc data_cap' inst_cap' addr_cap')
  qed
  have out_cap_ge7: "7 \<le> unat out_cap"
    using out_cap_ok spec_eq
    by (simp add: serialize_def Let_def magic_bytes_def varint_encode_length)
  have fixed_byte_step:
    "\<And>pos. unat pos < 6 \<Longrightarrow>
      serialize_byte_step_ok s out out_cap pos data (length ?data_bytes)
        inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule byte_step) (use out_cap_ge7 section_caps in simp_all)
  have no_dlen_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap 6 ?dlen dlen_n
        data (length ?data_bytes) inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use dlen_size out_cap_ok spec_eq dlen_size_unat section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have no_tgt_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap ((6 :: 32 word) + dlen_n) tgt_len tgt_n
        data (length ?data_bytes) inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use tgt_size out_cap_ok spec_eq dlen_size_unat size_unats dlen_size_le5
        section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have no_delta_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_byte_step_ok s out out_cap ((6 :: 32 word) + dlen_n + tgt_n)
        data (length ?data_bytes) inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule byte_step)
      (use out_cap_ok spec_eq dlen_size_unat size_unats dlen_size_le5
        size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have no_data_len_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap ((7 :: 32 word) + (dlen_n + tgt_n))
        ?data_len data_n data (length ?data_bytes)
        inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use data_size out_cap_ok spec_eq dlen_size_unat size_unats dlen_size_le5
        size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have no_inst_len_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap
        ((7 :: 32 word) + (dlen_n + tgt_n) + data_n)
        ?inst_len inst_n data (length ?data_bytes)
        inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use inst_size out_cap_ok spec_eq dlen_size_unat size_unats dlen_size_le5
        size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have no_addr_len_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap
        ((7 :: 32 word) + (dlen_n + tgt_n) + data_n + inst_n)
        ?addr_len addr_n data (length ?data_bytes)
        inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use addr_size out_cap_ok spec_eq dlen_size_unat size_unats dlen_size_le5
        size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have no_data_copy_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_copy_step_ok s out out_cap
        ((7 :: 32 word) + (dlen_n + tgt_n) + data_n + inst_n + addr_n)
        data ?data_len inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule data_copy_step)
      (use out_cap_ok spec_eq dlen_size_unat size_unats dlen_size_le5
        size_le5 data_len section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have no_inst_copy_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_copy_step_ok s out out_cap
        ((7 :: 32 word) + (dlen_n + tgt_n) + data_n + inst_n + addr_n + ?data_len)
        inst ?inst_len data (length ?data_bytes) addr (length ?addr_bytes)"
    by (rule inst_copy_step)
      (use out_cap_ok spec_eq dlen_size_unat size_unats dlen_size_le5
        size_le5 data_len inst_len section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have no_addr_copy_step:
    "src_bytes = [] \<Longrightarrow>
      serialize_copy_step_ok s out out_cap
        ((7 :: 32 word) + (dlen_n + tgt_n) + data_n + inst_n + addr_n +
          ?data_len + ?inst_len)
        addr ?addr_len data (length ?data_bytes) inst (length ?inst_bytes)"
    by (rule addr_copy_step)
      (use out_cap_ok spec_eq dlen_size_unat size_unats dlen_size_le5
        size_le5 data_len inst_len addr_len section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_desc_len_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap 6 src_len src_n
        data (length ?data_bytes) inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use src_size out_cap_ok spec_eq src_size_unat section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_pos_step':
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap ((6 :: 32 word) + src_n) 0 1
        data (length ?data_bytes) inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule src_pos_step) (use section_caps in simp_all)
  have src_dlen_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap ((7 :: 32 word) + src_n) ?dlen dlen_n
        data (length ?data_bytes) inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use dlen_size out_cap_ok spec_eq src_size_unat dlen_size_unat size_le5
        dlen_size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_tgt_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap ((7 :: 32 word) + src_n + dlen_n)
        tgt_len tgt_n data (length ?data_bytes)
        inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use tgt_size out_cap_ok spec_eq src_size_unat dlen_size_unat size_unats
        size_le5 dlen_size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_delta_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_byte_step_ok s out out_cap ((7 :: 32 word) + src_n + dlen_n + tgt_n)
        data (length ?data_bytes) inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule byte_step)
      (use out_cap_ok spec_eq src_size_unat dlen_size_unat size_unats
        size_le5 dlen_size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_data_len_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap
        ((8 :: 32 word) + (src_n + (dlen_n + tgt_n)))
        ?data_len data_n data (length ?data_bytes)
        inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use data_size out_cap_ok spec_eq src_size_unat dlen_size_unat size_unats
        size_le5 dlen_size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_inst_len_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap
        ((8 :: 32 word) + (src_n + (dlen_n + tgt_n)) + data_n)
        ?inst_len inst_n data (length ?data_bytes)
        inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use inst_size out_cap_ok spec_eq src_size_unat dlen_size_unat size_unats
        size_le5 dlen_size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_addr_len_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_varint_step_ok s out out_cap
        ((8 :: 32 word) + (src_n + (dlen_n + tgt_n)) + data_n + inst_n)
        ?addr_len addr_n data (length ?data_bytes)
        inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule varint_step)
      (use addr_size out_cap_ok spec_eq src_size_unat dlen_size_unat size_unats
        size_le5 dlen_size_le5 section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_data_copy_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_copy_step_ok s out out_cap
        ((8 :: 32 word) + (src_n + (dlen_n + tgt_n)) + data_n + inst_n + addr_n)
        data ?data_len inst (length ?inst_bytes) addr (length ?addr_bytes)"
    by (rule data_copy_step)
      (use out_cap_ok spec_eq src_size_unat dlen_size_unat size_unats
        size_le5 dlen_size_le5 data_len section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_inst_copy_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_copy_step_ok s out out_cap
        ((8 :: 32 word) + (src_n + (dlen_n + tgt_n)) + data_n + inst_n + addr_n +
          ?data_len)
        inst ?inst_len data (length ?data_bytes) addr (length ?addr_bytes)"
    by (rule inst_copy_step)
      (use out_cap_ok spec_eq src_size_unat dlen_size_unat size_unats
        size_le5 dlen_size_le5 data_len inst_len section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have src_addr_copy_step:
    "src_bytes \<noteq> [] \<Longrightarrow>
      serialize_copy_step_ok s out out_cap
        ((8 :: 32 word) + (src_n + (dlen_n + tgt_n)) + data_n + inst_n + addr_n +
          ?data_len + ?inst_len)
        addr ?addr_len data (length ?data_bytes) inst (length ?inst_bytes)"
    by (rule addr_copy_step)
      (use out_cap_ok spec_eq src_size_unat dlen_size_unat size_unats
        size_le5 dlen_size_le5 data_len inst_len addr_len section_caps in
        \<open>auto simp: serialize_def Let_def magic_bytes_def varint_encode_length
          word_le_nat_alt unat_word_ariths\<close>)
  have raw:
    "serialize' out out_cap src_len tgt_len
        data ?data_len inst ?inst_len addr ?addr_len \<bullet> s
     \<lbrace> \<lambda>r t. r = Result
          (if src_bytes = []
           then (7 :: 32 word) + (dlen_n + tgt_n) + data_n + inst_n + addr_n +
             ?data_len + ?inst_len + ?addr_len
           else (8 :: 32 word) + (src_n + (dlen_n + tgt_n)) +
             data_n + inst_n + addr_n + ?data_len + ?inst_len + ?addr_len) \<and>
        heap_bytes t out
          (unat
            (if src_bytes = []
             then (7 :: 32 word) + (dlen_n + tgt_n) + data_n + inst_n + addr_n +
               ?data_len + ?inst_len + ?addr_len
             else (8 :: 32 word) + (src_n + (dlen_n + tgt_n)) +
               data_n + inst_n + addr_n + ?data_len + ?inst_len + ?addr_len)) =
          serialize src_bytes tgt_bytes ?data_bytes ?inst_bytes ?addr_bytes \<and>
        heap_typing t = heap_typing s \<rbrace>"
    apply (rule serialize'_writes_serialize[
      where src = src_bytes and tgt = tgt_bytes
        and data_bytes = ?data_bytes and inst_bytes = ?inst_bytes
        and addr_bytes = ?addr_bytes
        and src_n = src_n and tgt_n = tgt_n and data_n = data_n
        and inst_n = inst_n and addr_n = addr_n and dlen_n = dlen_n])
                                      apply (rule input_len(1))
                                     apply (rule input_len(2))
                                    apply (rule data_len)
                                   apply (rule inst_len)
                                  apply (rule addr_len)
                                 apply (rule data_heap)
                                apply (rule inst_heap)
                               apply (rule addr_heap)
                              apply (rule src_size)
                             apply (rule tgt_size)
                            apply (rule data_size)
                           apply (rule inst_size)
                          apply (rule addr_size)
                         apply (rule dlen_size)
                        apply (rule dlen_unat)
	                       apply (simp add: src_bytes)
	                      apply (simp add: dlen_bytes)
	                     apply (simp add: tgt_bytes)
	                    apply (simp add: data_bytes)
	                   apply (simp add: inst_bytes)
	                  apply (simp add: addr_bytes)
		                 apply (rule fixed_byte_step; simp)
		                apply (rule fixed_byte_step; simp)
		               apply (rule fixed_byte_step; simp)
		              apply (rule fixed_byte_step; simp)
		             apply (rule fixed_byte_step; simp)
		            apply (rule fixed_byte_step; simp)
			           apply (rule no_dlen_step; simp)
			          apply (rule no_tgt_step; simp)
			         apply (rule no_delta_step; simp)
			        apply (rule no_data_len_step; simp)
			       apply (rule no_inst_len_step; simp)
			      apply (rule no_addr_len_step; simp)
			     apply (rule no_data_copy_step; simp)
			    apply (rule no_inst_copy_step; simp)
			   apply (rule no_addr_copy_step; simp)
			  apply (rule src_desc_len_step; simp)
			 apply (rule src_pos_step'; simp)
		apply (rule src_dlen_step; simp)
	       apply (rule src_tgt_step; simp)
	      apply (rule src_delta_step; simp)
	     apply (rule src_data_len_step; simp)
	    apply (rule src_inst_len_step; simp)
	   apply (rule src_addr_len_step; simp)
	  apply (rule src_data_copy_step; simp)
	  apply (rule src_inst_copy_step; simp)
	apply (rule src_addr_copy_step; simp)
	    done
  have p_end_unat:
    "unat
      (if src_bytes = []
       then (7 :: 32 word) + (dlen_n + tgt_n) + data_n + inst_n + addr_n +
         ?data_len + ?inst_len + ?addr_len
       else (8 :: 32 word) + (src_n + (dlen_n + tgt_n)) +
         data_n + inst_n + addr_n + ?data_len + ?inst_len + ?addr_len) =
     length (serialize src_bytes tgt_bytes ?data_bytes ?inst_bytes ?addr_bytes)"
  proof (cases "src_bytes = []")
    case True
    show ?thesis
      using True spec_eq encoded_len_word dlen_size_unat size_unats
        data_len inst_len addr_len dlen_size_le5 size_le5
      by (simp add: serialize_def Let_def magic_bytes_def varint_encode_length
        word_le_nat_alt unat_word_ariths)
  next
    case False
    show ?thesis
      using False spec_eq encoded_len_word src_size_unat[OF False]
        dlen_size_unat size_unats data_len inst_len addr_len
        dlen_size_le5 size_le5
      by (simp add: serialize_def Let_def magic_bytes_def varint_encode_length
        word_le_nat_alt unat_word_ariths)
  qed
  show ?thesis
    apply (rule runs_to_weaken[OF raw])
    using spec_eq encoded_len_word p_end_unat
    by (auto simp: encoder_success_post_def)
qed

lemma vcdiff_encode'_compose_phases_topdown:
  fixes out src tgt pending data inst addr :: "8 word ptr"
    and out_cap src_len tgt_len pending_cap data_cap inst_cap addr_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
        "encoder_input_rel s src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and pending_cap_ok: "unat tgt_len \<le> unat pending_cap"
      and src_len_word: "unat src_len < unat (no_entry32 :: 32 word)"
      and fit:
        "sections_fit_32 src_bytes tgt_bytes
          (encode_window_full_spec src_bytes tgt_bytes)"
      and out_cap_ok:
        "length (encode_spec src_bytes tgt_bytes) \<le> unat out_cap"
      and encoded_len_word:
        "length (encode_spec src_bytes tgt_bytes) < 2 ^ 32"
      and spec_eq:
        "encode_spec src_bytes tgt_bytes =
          serialize src_bytes tgt_bytes
            (efr_data (encode_window_full_spec src_bytes tgt_bytes))
            (efr_inst (encode_window_full_spec src_bytes tgt_bytes))
            (efr_addr (encode_window_full_spec src_bytes tgt_bytes))"
      and build_phase:
        "build_index' src src_len head_arr next_arr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               encoder_index_post s t src src_len tgt tgt_len head_arr next_arr
                 src_bytes tgt_bytes \<rbrace>"
      and window_phase:
        "\<And>s_index. encoder_index_post s s_index src src_len tgt tgt_len
             head_arr next_arr src_bytes tgt_bytes \<Longrightarrow>
           encode_window' src src_len tgt tgt_len head_arr next_arr
             data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet>
             s_index
           \<lbrace> \<lambda>r t. \<exists>sec.
               r = Result sec \<and>
               encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
               encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
               heap_bytes t src (unat src_len) = src_bytes \<and>
               heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
               heap_typing t = heap_typing s_index \<rbrace>"
      and serialize_phase:
        "\<And>s_window sec. \<lbrakk>
           encoder_window_post s_window data inst addr sec src_bytes tgt_bytes;
           encoder_window_caps_ok sec data_cap inst_cap addr_cap;
           heap_typing s_window = heap_typing s
         \<rbrakk> \<Longrightarrow>
           serialize' out out_cap src_len tgt_len
             data (sections_t_C.data_pos_C sec)
             inst (sections_t_C.inst_pos_C sec)
             addr (sections_t_C.addr_pos_C sec) \<bullet> s_window
           \<lbrace> \<lambda>r t. \<exists>n.
               r = Result n \<and>
               encoder_success_post out src_bytes tgt_bytes n s_window t \<rbrace>"
  shows "vcdiff_encode' out out_cap src src_len tgt tgt_len head_arr next_arr
            pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>n.
               r = Result n \<and>
               encoder_success_post out src_bytes tgt_bytes n s t \<rbrace>"
proof -
  have cap_ok: "\<not> pending_cap < tgt_len"
    using pending_cap_ok by (simp add: word_less_nat_alt)
  have success_from_window:
    "\<And>s_index s_window n t.
      encoder_index_post s s_index src src_len tgt tgt_len head_arr next_arr
        src_bytes tgt_bytes \<Longrightarrow>
      heap_typing s_window = heap_typing s_index \<Longrightarrow>
      encoder_success_post out src_bytes tgt_bytes n s_window t \<Longrightarrow>
      encoder_success_post out src_bytes tgt_bytes n s t"
    by (auto simp: encoder_index_post_def encoder_success_post_def)
  show ?thesis
    unfolding vcdiff_encode'_def
    apply (simp add: cap_ok)
    apply (rule runs_to_bind)
     apply (rule runs_to_weaken[OF build_phase])
     apply simp
    subgoal for s_index
      apply (rule runs_to_bind)
       apply (rule runs_to_weaken[OF window_phase])
        apply assumption
       apply simp
      apply clarsimp
      subgoal for s_window sec
        apply (simp add: encoder_window_post_def)
        apply (rule runs_to_weaken[OF serialize_phase])
         apply (simp add: encoder_window_post_def)
        apply simp
        apply (simp add: encoder_index_post_def)
        using success_from_window
        by auto
      done
    done
qed

theorem vcdiff_encode'_writes_encode_spec_topdown:
  fixes out src tgt pending data inst addr :: "8 word ptr"
    and out_cap src_len tgt_len pending_cap data_cap inst_cap addr_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
        "encoder_input_rel s src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and pending_cap_ok: "unat tgt_len \<le> unat pending_cap"
      and src_len_word: "unat src_len < unat (no_entry32 :: 32 word)"
      and head_valid:
        "\<And>h. h < hash_size \<Longrightarrow>
          ptr_valid (heap_typing s) (head_arr +\<^sub>p int h)"
      and next_valid:
        "\<And>p. p < unat src_len \<Longrightarrow>
          ptr_valid (heap_typing s) (next_arr +\<^sub>p int p)"
      and head_no_alias:
        "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
          head_arr +\<^sub>p int h \<noteq> head_arr +\<^sub>p int bucket"
      and next_no_alias:
        "\<And>q p. \<lbrakk>q < unat src_len; p < unat src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      and next_head_disjoint:
        "\<And>h p. \<lbrakk>h < hash_size; p < unat src_len\<rbrakk> \<Longrightarrow>
          head_arr +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
      and head_next_disjoint:
        "\<And>q bucket. \<lbrakk>q < unat src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> head_arr +\<^sub>p int bucket"
      and fit:
        "sections_fit_32 src_bytes tgt_bytes
          (encode_window_full_spec src_bytes tgt_bytes)"
      and out_cap_ok:
        "length (encode_spec src_bytes tgt_bytes) \<le> unat out_cap"
      and encoded_len_word:
        "length (encode_spec src_bytes tgt_bytes) < 2 ^ 32"
  shows "vcdiff_encode' out out_cap src src_len tgt tgt_len head_arr next_arr
            pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>n.
               r = Result n \<and>
               encoder_success_post out src_bytes tgt_bytes n s t \<rbrace>"
proof -
  have spec_eq:
    "encode_spec src_bytes tgt_bytes =
      serialize src_bytes tgt_bytes
        (efr_data (encode_window_full_spec src_bytes tgt_bytes))
        (efr_inst (encode_window_full_spec src_bytes tgt_bytes))
        (efr_addr (encode_window_full_spec src_bytes tgt_bytes))"
    by (rule encode_spec_fast_path_topdown[OF fit])
  have build_phase:
    "build_index' src src_len head_arr next_arr \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           encoder_index_post s t src src_len tgt tgt_len head_arr next_arr
             src_bytes tgt_bytes \<rbrace>"
    by (rule vcdiff_encode'_build_index_phase_topdown[
        OF input buffers src_len_word head_valid next_valid head_no_alias
          next_no_alias next_head_disjoint head_next_disjoint])
  have window_phase:
    "\<And>s_index. encoder_index_post s s_index src src_len tgt tgt_len
       head_arr next_arr src_bytes tgt_bytes \<Longrightarrow>
     encode_window' src src_len tgt tgt_len head_arr next_arr
       data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s_index
     \<lbrace> \<lambda>r t. \<exists>sec.
         r = Result sec \<and>
         encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
         encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
         heap_bytes t src (unat src_len) = src_bytes \<and>
         heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
         heap_typing t = heap_typing s_index \<rbrace>"
  proof -
    fix s_index
    assume index:
      "encoder_index_post s s_index src src_len tgt tgt_len head_arr next_arr
        src_bytes tgt_bytes"
    show "encode_window' src src_len tgt tgt_len head_arr next_arr
       data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s_index
     \<lbrace> \<lambda>r t. \<exists>sec.
         r = Result sec \<and>
         encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
         encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
         heap_bytes t src (unat src_len) = src_bytes \<and>
         heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
         heap_typing t = heap_typing s_index \<rbrace>"
      by (rule vcdiff_encode'_encode_window_phase_topdown[
          OF input buffers index fit])
  qed
  have serialize_phase:
    "\<And>s_window sec. \<lbrakk>
       encoder_window_post s_window data inst addr sec src_bytes tgt_bytes;
       encoder_window_caps_ok sec data_cap inst_cap addr_cap;
       heap_typing s_window = heap_typing s
     \<rbrakk> \<Longrightarrow>
     serialize' out out_cap src_len tgt_len
       data (sections_t_C.data_pos_C sec)
       inst (sections_t_C.inst_pos_C sec)
       addr (sections_t_C.addr_pos_C sec) \<bullet> s_window
     \<lbrace> \<lambda>r t. \<exists>n.
         r = Result n \<and>
         encoder_success_post out src_bytes tgt_bytes n s_window t \<rbrace>"
  proof -
    fix s_window sec
    assume window:
      "encoder_window_post s_window data inst addr sec src_bytes tgt_bytes"
    assume window_caps:
      "encoder_window_caps_ok sec data_cap inst_cap addr_cap"
    assume typing: "heap_typing s_window = heap_typing s"
    show "serialize' out out_cap src_len tgt_len
       data (sections_t_C.data_pos_C sec)
       inst (sections_t_C.inst_pos_C sec)
       addr (sections_t_C.addr_pos_C sec) \<bullet> s_window
     \<lbrace> \<lambda>r t. \<exists>n.
         r = Result n \<and>
         encoder_success_post out src_bytes tgt_bytes n s_window t \<rbrace>"
      by (rule vcdiff_encode'_serialize_phase_topdown[
          OF input buffers fit out_cap_ok encoded_len_word typing window window_caps])
  qed
  show ?thesis
    by (rule vcdiff_encode'_compose_phases_topdown[
        OF input buffers pending_cap_ok src_len_word fit out_cap_ok
          encoded_len_word spec_eq build_phase window_phase serialize_phase])
qed

end

end
