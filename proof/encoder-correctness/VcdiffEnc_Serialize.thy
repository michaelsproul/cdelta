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
  shows "build_index' src src_len head_arr next_arr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               encoder_index_post s t src src_len tgt tgt_len head_arr next_arr
                 src_bytes tgt_bytes \<rbrace>"
  sorry

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
               heap_bytes t src (unat src_len) = src_bytes \<and>
               heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
               heap_typing t = heap_typing s \<rbrace>"
  sorry

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
      and window:
        "encoder_window_post s data inst addr sec src_bytes tgt_bytes"
  shows "serialize' out out_cap src_len tgt_len
            data (sections_t_C.data_pos_C sec)
            inst (sections_t_C.inst_pos_C sec)
            addr (sections_t_C.addr_pos_C sec) \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>n.
               r = Result n \<and>
               encoder_success_post out src_bytes tgt_bytes n s t \<rbrace>"
  sorry

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
               heap_bytes t src (unat src_len) = src_bytes \<and>
               heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
               heap_typing t = heap_typing s_index \<rbrace>"
      and serialize_phase:
        "\<And>s_window sec. encoder_window_post s_window data inst addr sec
             src_bytes tgt_bytes \<Longrightarrow>
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
  sorry

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
        OF input buffers src_len_word])
  have window_phase:
    "\<And>s_index. encoder_index_post s s_index src src_len tgt tgt_len
       head_arr next_arr src_bytes tgt_bytes \<Longrightarrow>
     encode_window' src src_len tgt tgt_len head_arr next_arr
       data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s_index
     \<lbrace> \<lambda>r t. \<exists>sec.
         r = Result sec \<and>
         encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
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
         heap_bytes t src (unat src_len) = src_bytes \<and>
         heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
         heap_typing t = heap_typing s_index \<rbrace>"
      by (rule vcdiff_encode'_encode_window_phase_topdown[
          OF input buffers index fit])
  qed
  have serialize_phase:
    "\<And>s_window sec. encoder_window_post s_window data inst addr sec
       src_bytes tgt_bytes \<Longrightarrow>
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
    show "serialize' out out_cap src_len tgt_len
       data (sections_t_C.data_pos_C sec)
       inst (sections_t_C.inst_pos_C sec)
       addr (sections_t_C.addr_pos_C sec) \<bullet> s_window
     \<lbrace> \<lambda>r t. \<exists>n.
         r = Result n \<and>
         encoder_success_post out src_bytes tgt_bytes n s_window t \<rbrace>"
      by (rule vcdiff_encode'_serialize_phase_topdown[
          OF input buffers fit out_cap_ok encoded_len_word window])
  qed
  show ?thesis
    by (rule vcdiff_encode'_compose_phases_topdown[
        OF input buffers pending_cap_ok src_len_word fit out_cap_ok
          encoded_len_word spec_eq build_phase window_phase serialize_phase])
qed

end

end
