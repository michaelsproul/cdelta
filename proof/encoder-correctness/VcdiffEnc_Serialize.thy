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

lemma heap_bytes_update_disjoint_prefix:
  assumes disj: "bufs_disjoint out out_cap buf buf_cap"
      and pos_lt: "unat pos < buf_cap"
      and out_n_le: "out_n \<le> out_cap"
  shows "heap_bytes (heap_w8_update
            (\<lambda>h. h(buf +\<^sub>p uint pos := b)) s) out out_n =
         heap_bytes s out out_n"
  apply (rule heap_bytes_update_outside)
  apply (intro allI impI)
  subgoal for i
    by (rule bufs_disjoint_word_point_rightD[OF disj _ pos_lt])
      (use out_n_le in simp)
  done

lemma heap_bytes_word_zero_update_append:
  fixes pos cap :: "32 word"
  assumes pos_lt: "pos < cap"
      and dist: "ptr_range_distinct buf (unat cap)"
  shows "heap_bytes_word (heap_w8_update
            (\<lambda>h. h(buf +\<^sub>p uint pos := b)) s) buf 0 (pos + 1) =
         heap_bytes_word s buf 0 pos @ [b]"
proof -
  have pos_suc: "unat (pos + 1) = Suc (unat pos)"
    by (rule unat_suc_word_less[OF pos_lt])
  have dist_suc: "ptr_range_distinct buf (Suc (unat pos))"
    by (rule ptr_range_distinct_mono[OF dist])
      (use pos_lt in \<open>simp add: word_less_nat_alt\<close>)
  have append_int:
    "heap_bytes (heap_w8_update
        (\<lambda>h. h(buf +\<^sub>p int (unat pos) := b)) s) buf
        (Suc (unat pos)) =
     heap_bytes s buf (unat pos) @ [b]"
    by (rule heap_bytes_extend_distinct[OF dist_suc])
  have append:
    "heap_bytes (heap_w8_update
        (\<lambda>h. h(buf +\<^sub>p uint pos := b)) s) buf (Suc (unat pos)) =
     heap_bytes s buf (unat pos) @ [b]"
    using append_int by (simp only: uint_nat)
  show ?thesis
    using append pos_suc
    by (simp add: heap_bytes_word_zero)
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

lemma encoder_buffers_ok_pending_ptr_valid:
  fixes s0 t :: lifted_globals
    and len :: "32 word"
  assumes buffers:
        "encoder_buffers_ok s0 out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and typing: "heap_typing t = heap_typing s0"
      and len_le: "unat len \<le> unat pending_cap"
  shows "\<forall>j < unat len.
      ptr_valid (heap_typing t)
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
proof (intro allI impI)
  fix j
  assume j_lt: "j < unat len"
  have pending_ok0: "buf_valid s0 pending (unat pending_cap)"
    using buffers by (simp add: encoder_buffers_ok_def)
  have pending_ok: "buf_valid t pending (unat pending_cap)"
    using pending_ok0 typing by (simp add: buf_valid_def)
  have no_overflow: "unat (0 :: 32 word) + unat len < 2 ^ 32"
    using unat_lt2p[of len] by simp
  have range: "unat (0 :: 32 word) + unat len \<le> unat pending_cap"
    using len_le by simp
  show "ptr_valid (heap_typing t)
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
    by (rule buf_valid_word_rangeD[
        OF pending_ok j_lt no_overflow range])
qed

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

lemma varint_size_nat_le_5_32:
  assumes n32: "n < 2 ^ 32"
  shows "varint_size n \<le> 5"
proof (cases "n = 0")
  case True
  then show ?thesis
    by (simp add: varint_size_def)
next
  case False
  have "n < 2 ^ 35"
    using n32 by simp
  then show ?thesis
    using num_digits_le_5[of n] False
    by (simp add: varint_size_def)
qed

lemma varint_size_nat_le_1_128:
  assumes n128: "n < 128"
  shows "varint_size n \<le> 1"
proof (cases "n = 0")
  case True
  then show ?thesis
    by (simp add: varint_size_def)
next
  case False
  have "n < 128 ^ (1 :: nat)"
    using n128 by simp
  then have "num_digits n \<le> 1"
    by (rule num_digits_le)
  then show ?thesis
    using False by (simp add: varint_size_def)
qed

lemma try_near_mode_len_le_best:
  "length (snd (try_near_mode c addr i best)) \<le> length (snd best)"
  by (auto simp: try_near_mode_def try_better_def Let_def split: if_splits)

lemma try_near_modes_len_le_best:
  "length (snd (try_near_modes c addr n best)) \<le> length (snd best)"
proof (induction n arbitrary: best)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "length (snd (try_near_modes c addr (Suc n) best)) \<le>
        length (snd (try_near_mode c addr (s_near - Suc n) best))"
    using Suc.IH by simp
  also have "... \<le> length (snd best)"
    by (rule try_near_mode_len_le_best)
  finally show ?case .
qed

lemma try_same_mode_len_le_best:
  "length (snd (try_same_mode c addr i best)) \<le> length (snd best)"
  by (auto simp: try_same_mode_def try_better_def Let_def split: if_splits)

lemma try_same_modes_len_le_best:
  "length (snd (try_same_modes c addr n best)) \<le> length (snd best)"
proof (induction n arbitrary: best)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "length (snd (try_same_modes c addr (Suc n) best)) \<le>
        length (snd (try_same_mode c addr (s_same - Suc n) best))"
    using Suc.IH by simp
  also have "... \<le> length (snd best)"
    by (rule try_same_mode_len_le_best)
  finally show ?case .
qed

lemma encode_address_cache_update_plus6_len_le1:
  assumes wf: "enc_cache_wf c"
  shows "length (case encode_address (cache_update c addr) (addr + 6) here of
          (_, bs, _) \<Rightarrow> bs) \<le> 1"
proof -
  have near_len: "length (near c) = s_near"
    and near_ptr_lt: "near_ptr c < s_near"
    using wf by (simp_all add: enc_cache_wf_def)
  have varint6_len: "length (varint_encode 6) \<le> 1"
    using varint_size_nat_le_1_128[of 6] by simp
  let ?c' = "cache_update c addr"
  let ?a = "addr + 6"
  have near_modes_len:
    "length (snd (try_near_modes ?c' ?a s_near best)) \<le> 1" for best
  proof -
    have cases:
      "near_ptr c = 0 \<or> near_ptr c = 1 \<or>
       near_ptr c = 2 \<or> near_ptr c = 3"
      using near_ptr_lt by (simp add: s_near_def) linarith
    then show ?thesis
    proof (elim disjE)
      assume np: "near_ptr c = 0"
      have hit:
        "length (snd (try_near_mode ?c' ?a 0 best)) \<le> 1"
        using near_len np varint6_len
        by (simp add: cache_update_def try_near_mode_def try_better_def
            s_near_def same_buckets_def)
      have "length (snd (try_near_modes ?c' ?a 3
              (try_near_mode ?c' ?a 0 best))) \<le>
            length (snd (try_near_mode ?c' ?a 0 best))"
        by (rule try_near_modes_len_le_best)
      moreover have
        "try_near_modes ?c' ?a s_near best =
         try_near_modes ?c' ?a 3 (try_near_mode ?c' ?a 0 best)"
        by (simp add: s_near_def eval_nat_numeral)
      then show ?thesis
        using hit calculation by simp
    next
      assume np: "near_ptr c = 1"
      let ?best1 = "try_near_mode ?c' ?a 0 best"
      have hit:
        "length (snd (try_near_mode ?c' ?a 1 ?best1)) \<le> 1"
        using near_len np varint6_len
        by (simp add: cache_update_def try_near_mode_def try_better_def
            s_near_def same_buckets_def)
      have "length (snd (try_near_modes ?c' ?a 2
              (try_near_mode ?c' ?a 1 ?best1))) \<le>
            length (snd (try_near_mode ?c' ?a 1 ?best1))"
        by (rule try_near_modes_len_le_best)
      moreover have
        "try_near_modes ?c' ?a s_near best =
         try_near_modes ?c' ?a 2 (try_near_mode ?c' ?a 1 ?best1)"
        by (simp add: s_near_def eval_nat_numeral)
      then show ?thesis
        using hit calculation by simp
    next
      assume np: "near_ptr c = 2"
      let ?best1 = "try_near_mode ?c' ?a 0 best"
      let ?best2 = "try_near_mode ?c' ?a 1 ?best1"
      have hit:
        "length (snd (try_near_mode ?c' ?a 2 ?best2)) \<le> 1"
        using near_len np varint6_len
        by (simp add: cache_update_def try_near_mode_def try_better_def
            s_near_def same_buckets_def)
      have "length (snd (try_near_modes ?c' ?a 1
              (try_near_mode ?c' ?a 2 ?best2))) \<le>
            length (snd (try_near_mode ?c' ?a 2 ?best2))"
        by (rule try_near_modes_len_le_best)
      moreover have
        "try_near_modes ?c' ?a s_near best =
         try_near_modes ?c' ?a 1 (try_near_mode ?c' ?a 2 ?best2)"
        by (simp add: s_near_def eval_nat_numeral)
      then show ?thesis
        using hit calculation by simp
    next
      assume np: "near_ptr c = 3"
      let ?best1 = "try_near_mode ?c' ?a 0 best"
      let ?best2 = "try_near_mode ?c' ?a 1 ?best1"
      let ?best3 = "try_near_mode ?c' ?a 2 ?best2"
      have hit:
        "length (snd (try_near_mode ?c' ?a 3 ?best3)) \<le> 1"
        using near_len np varint6_len
        by (simp add: cache_update_def try_near_mode_def try_better_def
            s_near_def same_buckets_def)
      moreover have
        "try_near_modes ?c' ?a s_near best =
         try_near_mode ?c' ?a 3 ?best3"
        by (simp add: s_near_def eval_nat_numeral)
      then show ?thesis
        using calculation by simp
    qed
  qed
  have same_modes_len:
    "length (snd (try_same_modes ?c' ?a s_same
        (try_near_modes ?c' ?a s_near best))) \<le> 1" for best
  proof -
    have "length (snd (try_same_modes ?c' ?a s_same
            (try_near_modes ?c' ?a s_near best))) \<le>
          length (snd (try_near_modes ?c' ?a s_near best))"
      by (rule try_same_modes_len_le_best)
    then show ?thesis
      using near_modes_len[of best] by linarith
  qed
  show ?thesis
    using same_modes_len
    by (simp add: encode_address_def Let_def)
qed

lemma add_inst_bytes_length_le_self:
  assumes n_pos: "0 < n"
      and n32: "n < 2 ^ 32"
  shows "length (add_inst_bytes n) \<le> n"
proof (cases "1 \<le> n \<and> n \<le> 17")
  case True
  then show ?thesis
    by (simp add: add_inst_bytes_def find_single_add_opcode_def Let_def)
next
  case False
  have n_ge_18: "18 \<le> n"
    using n_pos False by linarith
  have size_le: "varint_size n \<le> 5"
    by (rule varint_size_nat_le_5_32[OF n32])
  show ?thesis
    using False n_ge_18 size_le
    by (simp add: add_inst_bytes_def find_single_add_opcode_def Let_def)
qed

lemma run_inst_bytes_length_le_self:
  assumes n_ge: "4 \<le> n"
      and n32: "n < 2 ^ 32"
  shows "length (run_inst_bytes n) \<le> n"
proof (cases "n < 128")
  case True
  have size_le: "varint_size n \<le> 1"
    by (rule varint_size_nat_le_1_128[OF True])
  show ?thesis
    using n_ge size_le
    by (simp add: run_inst_bytes_def find_single_run_opcode_def Let_def)
next
  case False
  have size_le: "varint_size n \<le> 5"
    by (rule varint_size_nat_le_5_32[OF n32])
  show ?thesis
    using False size_le
    by (simp add: run_inst_bytes_def find_single_run_opcode_def Let_def)
qed

lemma pending_slice_length:
  assumes a_le_b: "a \<le> b"
      and b_le_len: "b \<le> length pending"
  shows "length (pending_slice pending a b) = b - a"
  using assms
  by (simp add: pending_slice_def)

lemma flush_pending_emit_add_spec_growth:
  assumes a_le_i: "add_start \<le> i"
      and i_le_len: "i \<le> length pending"
      and pending32: "length pending < 2 ^ 32"
  shows
    "length (enc_data
        (flush_pending_emit_add_spec src_len pending add_start i st))
       \<le> length (enc_data st) + (i - add_start)"
    "length (enc_inst
        (flush_pending_emit_add_spec src_len pending add_start i st))
       \<le> length (enc_inst st) + (i - add_start)"
    "length (enc_addr
        (flush_pending_emit_add_spec src_len pending add_start i st)) =
       length (enc_addr st)"
proof -
  show data_growth:
    "length (enc_data
        (flush_pending_emit_add_spec src_len pending add_start i st))
       \<le> length (enc_data st) + (i - add_start)"
  proof (cases "add_start < i")
    case True
    let ?bs = "pending_slice pending add_start i"
    have bs_len: "length ?bs = i - add_start"
      by (rule pending_slice_length[OF a_le_i i_le_len])
    show ?thesis
      using True bs_len
      by (simp add: flush_pending_emit_add_spec_def
          emit_inst_spec_RAdd_sections_general)
  next
    case False
    then show ?thesis
      by (simp add: flush_pending_emit_add_spec_def)
  qed

  show inst_growth:
    "length (enc_inst
        (flush_pending_emit_add_spec src_len pending add_start i st))
       \<le> length (enc_inst st) + (i - add_start)"
  proof (cases "add_start < i")
    case True
    let ?bs = "pending_slice pending add_start i"
    have bs_len: "length ?bs = i - add_start"
      by (rule pending_slice_length[OF a_le_i i_le_len])
    have bs_pos: "0 < length ?bs"
      using True bs_len by simp
    have bs32: "length ?bs < 2 ^ 32"
      using bs_len i_le_len pending32 by linarith
    have inst_le: "length (add_inst_bytes (length ?bs)) \<le> length ?bs"
      by (rule add_inst_bytes_length_le_self[OF bs_pos bs32])
    have inst_eq:
      "length (enc_inst
        (flush_pending_emit_add_spec src_len pending add_start i st)) =
       length (enc_inst st) + length (add_inst_bytes (length ?bs))"
      using True
      by (simp add: flush_pending_emit_add_spec_def
          emit_inst_spec_RAdd_sections_general)
    show ?thesis
      using inst_eq inst_le bs_len by simp
  next
    case False
    then show ?thesis
      by (simp add: flush_pending_emit_add_spec_def)
  qed

  show addr_growth:
    "length (enc_addr
        (flush_pending_emit_add_spec src_len pending add_start i st)) =
       length (enc_addr st)"
    by (cases "add_start < i")
       (simp_all add: flush_pending_emit_add_spec_def
        emit_inst_spec_RAdd_sections_general)
qed

lemma flush_pending_emit_run_spec_growth:
  assumes i_lt_j: "i < j"
      and j_le_len: "j \<le> length pending"
      and run_ge: "min_run \<le> j - i"
      and pending32: "length pending < 2 ^ 32"
  shows
    "length (enc_data
        (flush_pending_emit_run_spec src_len pending i j st))
       \<le> length (enc_data st) + (j - i)"
    "length (enc_inst
        (flush_pending_emit_run_spec src_len pending i j st))
       \<le> length (enc_inst st) + (j - i)"
    "length (enc_addr
        (flush_pending_emit_run_spec src_len pending i j st)) =
       length (enc_addr st)"
proof -
  have run_len_ge: "4 \<le> j - i"
    using run_ge by (simp add: min_run_def)
  have run_len32: "j - i < 2 ^ 32"
    using j_le_len pending32 by linarith
  have inst_le: "length (run_inst_bytes (j - i)) \<le> j - i"
    by (rule run_inst_bytes_length_le_self[OF run_len_ge run_len32])
  show
    "length (enc_data
        (flush_pending_emit_run_spec src_len pending i j st))
       \<le> length (enc_data st) + (j - i)"
    "length (enc_inst
        (flush_pending_emit_run_spec src_len pending i j st))
       \<le> length (enc_inst st) + (j - i)"
    "length (enc_addr
        (flush_pending_emit_run_spec src_len pending i j st)) =
       length (enc_addr st)"
    using run_len_ge inst_le
    by (simp_all add: flush_pending_emit_run_spec_def
        emit_inst_spec_RRun_sections_general)
qed

lemma flush_pending_loop_spec_growth:
  assumes a_le_i: "add_start \<le> i"
      and i_le_len: "i \<le> length pending"
      and pending32: "length pending < 2 ^ 32"
  shows
    "length (enc_data
        (flush_pending_loop_spec src_len pending add_start i st))
       \<le> length (enc_data st) + (length pending - add_start)"
    "length (enc_inst
        (flush_pending_loop_spec src_len pending add_start i st))
       \<le> length (enc_inst st) + (length pending - add_start)"
    "length (enc_addr
        (flush_pending_loop_spec src_len pending add_start i st)) =
       length (enc_addr st)"
proof -
  have growth:
    "\<And>fuel. \<forall>(pending :: byte list) add_start i st.
      fuel = length pending - i \<longrightarrow>
      add_start \<le> i \<longrightarrow>
      i \<le> length pending \<longrightarrow>
      length pending < 2 ^ 32 \<longrightarrow>
      length (enc_data
        (flush_pending_loop_spec src_len pending add_start i st))
        \<le> length (enc_data st) + (length pending - add_start) \<and>
      length (enc_inst
        (flush_pending_loop_spec src_len pending add_start i st))
        \<le> length (enc_inst st) + (length pending - add_start) \<and>
      length (enc_addr
        (flush_pending_loop_spec src_len pending add_start i st)) =
        length (enc_addr st)"
  proof -
    fix fuel :: nat
    show "\<forall>(pending :: byte list) add_start i st.
      fuel = length pending - i \<longrightarrow>
      add_start \<le> i \<longrightarrow>
      i \<le> length pending \<longrightarrow>
      length pending < 2 ^ 32 \<longrightarrow>
      length (enc_data
        (flush_pending_loop_spec src_len pending add_start i st))
        \<le> length (enc_data st) + (length pending - add_start) \<and>
      length (enc_inst
        (flush_pending_loop_spec src_len pending add_start i st))
        \<le> length (enc_inst st) + (length pending - add_start) \<and>
      length (enc_addr
        (flush_pending_loop_spec src_len pending add_start i st)) =
        length (enc_addr st)"
    proof (induction fuel rule: nat_less_induct)
      case (1 fuel)
      show ?case
    proof (intro allI impI)
      fix pending :: "byte list"
      fix add_start i st
      assume fuel_eq: "fuel = length pending - i"
         and a_le_i: "add_start \<le> i"
         and i_le_len: "i \<le> length pending"
         and pending32: "length pending < 2 ^ 32"
      show "length (enc_data
          (flush_pending_loop_spec src_len pending add_start i st))
          \<le> length (enc_data st) + (length pending - add_start) \<and>
        length (enc_inst
          (flush_pending_loop_spec src_len pending add_start i st))
          \<le> length (enc_inst st) + (length pending - add_start) \<and>
        length (enc_addr
          (flush_pending_loop_spec src_len pending add_start i st)) =
          length (enc_addr st)"
    proof (cases "i < length pending")
      case i_lt_len: True
      let ?j = "pending_run_end pending i"
      have i_lt_j: "i < ?j"
        by (rule pending_run_end_gt[OF i_lt_len])
      have j_le_len: "?j \<le> length pending"
        by (rule pending_run_end_le[OF i_lt_len])
      have a_le_j: "add_start \<le> ?j"
        using a_le_i i_lt_j by simp
      have fuel_j_lt: "length pending - ?j < fuel"
        using fuel_eq i_lt_j j_le_len i_lt_len by simp
      show ?thesis
      proof (cases "min_run \<le> ?j - i")
        case run_ge: True
        let ?st_add =
          "flush_pending_emit_add_spec src_len pending add_start i st"
        let ?st_run =
          "flush_pending_emit_run_spec src_len pending i ?j ?st_add"
        have add:
          "length (enc_data ?st_add) \<le>
             length (enc_data st) + (i - add_start)"
          "length (enc_inst ?st_add) \<le>
             length (enc_inst st) + (i - add_start)"
          "length (enc_addr ?st_add) = length (enc_addr st)"
          by (rule flush_pending_emit_add_spec_growth[
              OF a_le_i i_le_len pending32])+
        have run:
          "length (enc_data ?st_run) \<le>
             length (enc_data ?st_add) + (?j - i)"
          "length (enc_inst ?st_run) \<le>
             length (enc_inst ?st_add) + (?j - i)"
          "length (enc_addr ?st_run) = length (enc_addr ?st_add)"
          by (rule flush_pending_emit_run_spec_growth[
              OF i_lt_j j_le_len run_ge pending32])+
        have st_run:
          "length (enc_data ?st_run) \<le>
             length (enc_data st) + (?j - add_start)"
          "length (enc_inst ?st_run) \<le>
             length (enc_inst st) + (?j - add_start)"
          "length (enc_addr ?st_run) = length (enc_addr st)"
          using add run a_le_i i_lt_j by auto
        have rec:
          "length (enc_data
            (flush_pending_loop_spec src_len pending ?j ?j ?st_run))
            \<le> length (enc_data ?st_run) + (length pending - ?j)"
          "length (enc_inst
            (flush_pending_loop_spec src_len pending ?j ?j ?st_run))
            \<le> length (enc_inst ?st_run) + (length pending - ?j)"
          "length (enc_addr
            (flush_pending_loop_spec src_len pending ?j ?j ?st_run)) =
            length (enc_addr ?st_run)"
        proof -
          have rec_all:
            "length (enc_data
              (flush_pending_loop_spec src_len pending ?j ?j ?st_run))
              \<le> length (enc_data ?st_run) + (length pending - ?j) \<and>
             length (enc_inst
              (flush_pending_loop_spec src_len pending ?j ?j ?st_run))
              \<le> length (enc_inst ?st_run) + (length pending - ?j) \<and>
             length (enc_addr
              (flush_pending_loop_spec src_len pending ?j ?j ?st_run)) =
              length (enc_addr ?st_run)"
            using "1.IH" fuel_j_lt j_le_len pending32 by auto
          show
            "length (enc_data
              (flush_pending_loop_spec src_len pending ?j ?j ?st_run))
              \<le> length (enc_data ?st_run) + (length pending - ?j)"
            "length (enc_inst
              (flush_pending_loop_spec src_len pending ?j ?j ?st_run))
              \<le> length (enc_inst ?st_run) + (length pending - ?j)"
            "length (enc_addr
              (flush_pending_loop_spec src_len pending ?j ?j ?st_run)) =
              length (enc_addr ?st_run)"
            using rec_all by auto
        qed
        have data:
          "length (enc_data
            (flush_pending_loop_spec src_len pending ?j ?j ?st_run))
            \<le> length (enc_data st) + (length pending - add_start)"
          using rec(1) st_run(1) a_le_j j_le_len by linarith
        have inst:
          "length (enc_inst
            (flush_pending_loop_spec src_len pending ?j ?j ?st_run))
            \<le> length (enc_inst st) + (length pending - add_start)"
          using rec(2) st_run(2) a_le_j j_le_len by linarith
	        have addr:
	          "length (enc_addr
	            (flush_pending_loop_spec src_len pending ?j ?j ?st_run)) =
	            length (enc_addr st)"
	          using rec(3) st_run(3) by simp
	        show ?thesis
	        proof -
	          have loop_eq:
	            "flush_pending_loop_spec src_len pending add_start i st =
	             flush_pending_loop_spec src_len pending ?j ?j ?st_run"
	            using i_lt_len run_ge
	            by (subst flush_pending_loop_spec.simps) (simp add: Let_def)
	          show ?thesis
	            using loop_eq data inst addr by simp
	        qed
      next
        case short: False
        have rec:
          "length (enc_data
            (flush_pending_loop_spec src_len pending add_start ?j st))
            \<le> length (enc_data st) + (length pending - add_start)"
          "length (enc_inst
            (flush_pending_loop_spec src_len pending add_start ?j st))
            \<le> length (enc_inst st) + (length pending - add_start)"
          "length (enc_addr
            (flush_pending_loop_spec src_len pending add_start ?j st)) =
            length (enc_addr st)"
        proof -
          have rec_all:
            "length (enc_data
              (flush_pending_loop_spec src_len pending add_start ?j st))
              \<le> length (enc_data st) + (length pending - add_start) \<and>
             length (enc_inst
              (flush_pending_loop_spec src_len pending add_start ?j st))
              \<le> length (enc_inst st) + (length pending - add_start) \<and>
             length (enc_addr
              (flush_pending_loop_spec src_len pending add_start ?j st)) =
              length (enc_addr st)"
            using "1.IH" fuel_j_lt a_le_j j_le_len pending32 by auto
          show
            "length (enc_data
              (flush_pending_loop_spec src_len pending add_start ?j st))
              \<le> length (enc_data st) + (length pending - add_start)"
            "length (enc_inst
              (flush_pending_loop_spec src_len pending add_start ?j st))
              \<le> length (enc_inst st) + (length pending - add_start)"
            "length (enc_addr
              (flush_pending_loop_spec src_len pending add_start ?j st)) =
              length (enc_addr st)"
            using rec_all by auto
	        qed
	        show ?thesis
	        proof -
	          have loop_eq:
	            "flush_pending_loop_spec src_len pending add_start i st =
	             flush_pending_loop_spec src_len pending add_start ?j st"
	            using i_lt_len short
	            by (subst flush_pending_loop_spec.simps) (simp add: Let_def)
	          show ?thesis
	            using loop_eq rec by simp
	        qed
      qed
    next
      case not_lt: False
      have i_eq_len: "i = length pending"
        using not_lt i_le_len by simp
      have add:
        "length (enc_data
          (flush_pending_emit_add_spec src_len pending add_start
            (length pending) st))
          \<le> length (enc_data st) + (length pending - add_start)"
        "length (enc_inst
          (flush_pending_emit_add_spec src_len pending add_start
            (length pending) st))
          \<le> length (enc_inst st) + (length pending - add_start)"
        "length (enc_addr
          (flush_pending_emit_add_spec src_len pending add_start
            (length pending) st)) =
          length (enc_addr st)"
        by (rule flush_pending_emit_add_spec_growth(1)[
              OF _ order_refl pending32],
            use a_le_i i_eq_len in simp)
           (rule flush_pending_emit_add_spec_growth(2)[
              OF _ order_refl pending32],
            use a_le_i i_eq_len in simp,
            rule flush_pending_emit_add_spec_growth(3)[
              OF _ order_refl pending32],
            use a_le_i i_eq_len in simp)
      show ?thesis
      proof -
        have loop_eq:
          "flush_pending_loop_spec src_len pending add_start i st =
           (flush_pending_emit_add_spec src_len pending add_start
             (length pending) st)\<lparr>enc_pending := []\<rparr>"
          using not_lt
          by (subst flush_pending_loop_spec.simps) simp
        show ?thesis
          using add loop_eq by simp
      qed
    qed
    qed
    qed
  qed
  show
    "length (enc_data
        (flush_pending_loop_spec src_len pending add_start i st))
       \<le> length (enc_data st) + (length pending - add_start)"
    "length (enc_inst
        (flush_pending_loop_spec src_len pending add_start i st))
       \<le> length (enc_inst st) + (length pending - add_start)"
    "length (enc_addr
        (flush_pending_loop_spec src_len pending add_start i st)) =
       length (enc_addr st)"
    using growth[of "length pending - i"] a_le_i i_le_len pending32 by auto
qed

lemma flush_pending_emit_add_spec_mono:
  shows
    "length (enc_data st) \<le>
       length (enc_data
        (flush_pending_emit_add_spec src_len pending add_start i st))"
    "length (enc_inst st) \<le>
       length (enc_inst
        (flush_pending_emit_add_spec src_len pending add_start i st))"
    "length (enc_addr
        (flush_pending_emit_add_spec src_len pending add_start i st)) =
       length (enc_addr st)"
  by (cases "add_start < i")
     (simp_all add: flush_pending_emit_add_spec_def
        emit_inst_spec_RAdd_sections_general)

lemma flush_pending_emit_run_spec_mono:
  shows
    "length (enc_data st) \<le>
       length (enc_data
        (flush_pending_emit_run_spec src_len pending i j st))"
    "length (enc_inst st) \<le>
       length (enc_inst
        (flush_pending_emit_run_spec src_len pending i j st))"
    "length (enc_addr
        (flush_pending_emit_run_spec src_len pending i j st)) =
       length (enc_addr st)"
  by (simp_all add: flush_pending_emit_run_spec_def
      emit_inst_spec_RRun_sections_general)

lemma flush_pending_loop_spec_mono:
  assumes a_le_i: "add_start \<le> i"
      and i_le_len: "i \<le> length pending"
  shows
    "length (enc_data st) \<le>
       length (enc_data
        (flush_pending_loop_spec src_len pending add_start i st))"
    "length (enc_inst st) \<le>
       length (enc_inst
        (flush_pending_loop_spec src_len pending add_start i st))"
    "length (enc_addr
        (flush_pending_loop_spec src_len pending add_start i st)) =
       length (enc_addr st)"
proof -
  have mono:
    "\<And>fuel. \<forall>(pending :: byte list) add_start i st.
      fuel = length pending - i \<longrightarrow>
      add_start \<le> i \<longrightarrow>
      i \<le> length pending \<longrightarrow>
      length (enc_data st) \<le>
        length (enc_data
          (flush_pending_loop_spec src_len pending add_start i st)) \<and>
      length (enc_inst st) \<le>
        length (enc_inst
          (flush_pending_loop_spec src_len pending add_start i st)) \<and>
      length (enc_addr
          (flush_pending_loop_spec src_len pending add_start i st)) =
        length (enc_addr st)"
  proof -
    fix fuel :: nat
    show "\<forall>(pending :: byte list) add_start i st.
      fuel = length pending - i \<longrightarrow>
      add_start \<le> i \<longrightarrow>
      i \<le> length pending \<longrightarrow>
      length (enc_data st) \<le>
        length (enc_data
          (flush_pending_loop_spec src_len pending add_start i st)) \<and>
      length (enc_inst st) \<le>
        length (enc_inst
          (flush_pending_loop_spec src_len pending add_start i st)) \<and>
      length (enc_addr
          (flush_pending_loop_spec src_len pending add_start i st)) =
        length (enc_addr st)"
    proof (induction fuel rule: nat_less_induct)
      case (1 fuel)
      show ?case
      proof (intro allI impI)
        fix pending :: "byte list"
        fix add_start i st
        assume fuel_eq: "fuel = length pending - i"
           and a_le_i: "add_start \<le> i"
           and i_le_len: "i \<le> length pending"
        show "length (enc_data st) \<le>
            length (enc_data
              (flush_pending_loop_spec src_len pending add_start i st)) \<and>
          length (enc_inst st) \<le>
            length (enc_inst
              (flush_pending_loop_spec src_len pending add_start i st)) \<and>
          length (enc_addr
              (flush_pending_loop_spec src_len pending add_start i st)) =
            length (enc_addr st)"
        proof (cases "i < length pending")
          case i_lt_len: True
          let ?j = "pending_run_end pending i"
          have i_lt_j: "i < ?j"
            by (rule pending_run_end_gt[OF i_lt_len])
          have j_le_len: "?j \<le> length pending"
            by (rule pending_run_end_le[OF i_lt_len])
          have a_le_j: "add_start \<le> ?j"
            using a_le_i i_lt_j by simp
          have fuel_j_lt: "length pending - ?j < fuel"
            using fuel_eq i_lt_j j_le_len i_lt_len by simp
          show ?thesis
          proof (cases "min_run \<le> ?j - i")
            case run_ge: True
            let ?st_add =
              "flush_pending_emit_add_spec src_len pending add_start i st"
            let ?st_run =
              "flush_pending_emit_run_spec src_len pending i ?j ?st_add"
            have add:
              "length (enc_data st) \<le> length (enc_data ?st_add)"
              "length (enc_inst st) \<le> length (enc_inst ?st_add)"
              "length (enc_addr ?st_add) = length (enc_addr st)"
              by (rule flush_pending_emit_add_spec_mono)+
            have run:
              "length (enc_data ?st_add) \<le> length (enc_data ?st_run)"
              "length (enc_inst ?st_add) \<le> length (enc_inst ?st_run)"
              "length (enc_addr ?st_run) = length (enc_addr ?st_add)"
              by (rule flush_pending_emit_run_spec_mono)+
            have rec_all:
              "length (enc_data ?st_run) \<le>
                length (enc_data
                  (flush_pending_loop_spec src_len pending ?j ?j ?st_run)) \<and>
               length (enc_inst ?st_run) \<le>
                length (enc_inst
                  (flush_pending_loop_spec src_len pending ?j ?j ?st_run)) \<and>
               length (enc_addr
                  (flush_pending_loop_spec src_len pending ?j ?j ?st_run)) =
                length (enc_addr ?st_run)"
              using "1.IH" fuel_j_lt j_le_len by auto
            have loop_eq:
              "flush_pending_loop_spec src_len pending add_start i st =
               flush_pending_loop_spec src_len pending ?j ?j ?st_run"
              using i_lt_len run_ge
              by (subst flush_pending_loop_spec.simps) (simp add: Let_def)
            show ?thesis
              using add run rec_all loop_eq by auto
          next
            case short: False
            have rec_all:
              "length (enc_data st) \<le>
                length (enc_data
                  (flush_pending_loop_spec src_len pending add_start ?j st)) \<and>
               length (enc_inst st) \<le>
                length (enc_inst
                  (flush_pending_loop_spec src_len pending add_start ?j st)) \<and>
               length (enc_addr
                  (flush_pending_loop_spec src_len pending add_start ?j st)) =
                length (enc_addr st)"
              using "1.IH" fuel_j_lt a_le_j j_le_len by auto
            have loop_eq:
              "flush_pending_loop_spec src_len pending add_start i st =
               flush_pending_loop_spec src_len pending add_start ?j st"
              using i_lt_len short
              by (subst flush_pending_loop_spec.simps) (simp add: Let_def)
            show ?thesis
              using rec_all loop_eq by simp
          qed
        next
          case not_lt: False
          have loop_eq:
            "flush_pending_loop_spec src_len pending add_start i st =
             (flush_pending_emit_add_spec src_len pending add_start
               (length pending) st)\<lparr>enc_pending := []\<rparr>"
            using not_lt
            by (subst flush_pending_loop_spec.simps) simp
	          show ?thesis
	            using flush_pending_emit_add_spec_mono[
	              where st = st and src_len = src_len and pending = pending
	                and add_start = add_start and i = "length pending"] loop_eq
	            by simp
        qed
      qed
    qed
  qed
  show
    "length (enc_data st) \<le>
       length (enc_data
        (flush_pending_loop_spec src_len pending add_start i st))"
    "length (enc_inst st) \<le>
       length (enc_inst
        (flush_pending_loop_spec src_len pending add_start i st))"
    "length (enc_addr
        (flush_pending_loop_spec src_len pending add_start i st)) =
       length (enc_addr st)"
    using mono[of "length pending - i"] a_le_i i_le_len by auto
qed

lemma enc_sections_state_rel_lengths:
  assumes rel: "enc_sections_state_rel s data inst addr sec st"
  shows
    "length (enc_data st) = unat (sections_t_C.data_pos_C sec)"
    "length (enc_inst st) = unat (sections_t_C.inst_pos_C sec)"
    "length (enc_addr st) = unat (sections_t_C.addr_pos_C sec)"
  using enc_sections_state_relD[OF rel] by (metis heap_bytes_length)+

lemma heap_bytes_word_slice_eq_from_zero_frame:
  assumes frame:
    "heap_bytes_word t buf 0 len = heap_bytes_word s buf 0 len"
      and range: "unat off + unat sz \<le> unat len"
  shows "heap_bytes_word t buf off sz = heap_bytes_word s buf off sz"
  using heap_bytes_word_zero_take_drop[OF range, of t buf]
        heap_bytes_word_zero_take_drop[OF range, of s buf] frame
  by simp

lemma bufs_disjoint_uint_uintD:
  assumes disj: "bufs_disjoint p pn q qn"
      and i_lt: "unat i < pn"
      and j_lt: "unat j < qn"
  shows "p +\<^sub>p uint i \<noteq> q +\<^sub>p uint j"
proof
  assume eq: "p +\<^sub>p uint i = q +\<^sub>p uint j"
  have "p +\<^sub>p int (unat i) = q +\<^sub>p int (unat j)"
    using eq by (simp only: uint_nat)
  then show False
    using disj i_lt j_lt unfolding bufs_disjoint_def by blast
qed

lemma bufs_disjoint_int_uintD:
  assumes disj: "bufs_disjoint p pn q qn"
      and i_lt: "i < pn"
      and j_lt: "unat j < qn"
  shows "p +\<^sub>p int i \<noteq> q +\<^sub>p uint j"
proof
  assume eq: "p +\<^sub>p int i = q +\<^sub>p uint j"
  have "p +\<^sub>p int i = q +\<^sub>p int (unat j)"
    using eq by (simp only: uint_nat)
  then show False
    using disj i_lt j_lt unfolding bufs_disjoint_def by blast
qed

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

lemma emit_pending_add_chunk_from_loop_buffers:
  fixes s0 s :: lifted_globals
    and src tgt data inst addr pending :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap off sz
        pending_frame_off pending_frame_len :: "32 word"
    and spec_src_len :: nat
  assumes buffers:
    "encode_window_loop_buffers_ok s0 src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and typing: "heap_typing s = heap_typing s0"
    and rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and sz_ge: "(1 :: 32 word) \<le> sz"
    and pending_range: "unat off + unat sz \<le> unat pending_cap"
    and pending_frame_range:
      "unat pending_frame_off + unat pending_frame_len \<le>
       unat pending_cap"
    and data_room:
      "unat (sections_t_C.data_pos_C sec) + unat sz \<le>
       unat data_cap"
    and inst_room:
      "unat (sections_t_C.inst_pos_C sec) + 6 \<le>
       unat inst_cap"
    and addr_room:
      "unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec spec_src_len
                    (RAdd (heap_bytes_word s pending off sz)) spec_st)) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  obtain n where size: "varint_size' sz s = Some n"
    using varint_size'_some by blast
  have n_le5: "unat n \<le> 5"
    by (rule varint_size'_le5[OF size])
  have inst_valid0: "buf_valid s0 inst (unat inst_cap)"
    and data_valid0: "buf_valid s0 data (unat data_cap)"
    and pending_valid0: "buf_valid s0 pending (unat pending_cap)"
    and inst_dist: "ptr_range_distinct inst (unat inst_cap)"
    and data_dist: "ptr_range_distinct data (unat data_cap)"
    and pending_data: "bufs_disjoint pending (unat pending_cap) data (unat data_cap)"
    and pending_inst: "bufs_disjoint pending (unat pending_cap) inst (unat inst_cap)"
    and data_inst: "bufs_disjoint data (unat data_cap) inst (unat inst_cap)"
    and data_addr: "bufs_disjoint data (unat data_cap) addr (unat addr_cap)"
    and inst_addr: "bufs_disjoint inst (unat inst_cap) addr (unat addr_cap)"
    using buffers by (simp_all add: encode_window_loop_buffers_ok_def)
  have inst_valid: "buf_valid s inst (unat inst_cap)"
    and data_valid_buf: "buf_valid s data (unat data_cap)"
    and pending_valid_buf: "buf_valid s pending (unat pending_cap)"
    using inst_valid0 data_valid0 pending_valid0 typing
    by (simp_all add: buf_valid_def)
  have inst_byte_room:
    "unat (sections_t_C.inst_pos_C sec) < unat inst_cap"
    using inst_room by linarith
  have inst_cap32: "unat inst_cap < 2 ^ 32"
    using unat_lt2p[of inst_cap] by simp
  have data_cap32: "unat data_cap < 2 ^ 32"
    using unat_lt2p[of data_cap] by simp
  have pending_cap32: "unat pending_cap < 2 ^ 32"
    using unat_lt2p[of pending_cap] by simp
  have inst_var_room:
    "unat (sections_t_C.inst_pos_C sec + 1 + n) \<le>
     unat inst_cap"
    using inst_room n_le5 by unat_arith
  have inst_var_sum:
    "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
     unat inst_cap"
    using inst_room n_le5 by unat_arith
  have inst_var_no_overflow:
    "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
    using inst_var_sum inst_cap32 by linarith
  have data_no_overflow:
    "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
    using data_room data_cap32 by linarith
  have pending_no_overflow:
    "unat off + unat sz < 2 ^ 32"
    using pending_range pending_cap32 by linarith
  have pending_frame_no_overflow:
    "unat pending_frame_off + unat pending_frame_len < 2 ^ 32"
    using pending_frame_range pending_cap32 by linarith
  have inst_byte_ptr:
    "ptr_valid (heap_typing s)
      (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
    by (rule buf_valid_uintD[OF inst_valid inst_byte_room])
  have inst_byte_dist:
    "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
    by (rule ptr_range_distinct_mono[OF inst_dist])
       (use inst_byte_room in simp)
  show ?thesis
  proof (rule emit_pending_add_chunk_enc_sections_state_rel_preserves_heap_bytes_word[
      where src_len = spec_src_len, OF rel sz_ge size sec_ok])
    show "sections_t_C.inst_pos_C sec < inst_cap"
      using inst_byte_room by (simp add: word_less_nat_alt)
    show "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      by (rule inst_byte_ptr)
    show "ptr_range_distinct inst
          (Suc (unat (sections_t_C.inst_pos_C sec)))"
      by (rule inst_byte_dist)
    show "\<forall>i<unat (sections_t_C.data_pos_C sec).
          data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat (sections_t_C.data_pos_C sec)"
      have i_cap: "i < unat data_cap"
        using i_lt data_room by linarith
      show "data +\<^sub>p int i \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
        by (rule bufs_disjoint_int_uintD[
          OF data_inst i_cap inst_byte_room])
    qed
    show "\<forall>i<unat (sections_t_C.addr_pos_C sec).
          addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat (sections_t_C.addr_pos_C sec)"
      have i_cap: "i < unat addr_cap"
        using i_lt addr_room by linarith
      have addr_inst: "bufs_disjoint addr (unat addr_cap) inst (unat inst_cap)"
        using inst_addr by (simp add: bufs_disjoint_sym)
      show "addr +\<^sub>p int i \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
        by (rule bufs_disjoint_int_uintD[
          OF addr_inst i_cap inst_byte_room])
    qed
    show "\<forall>i<unat sz.
          pending +\<^sub>p uint (off + of_nat i) \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat sz"
      have pending_i_cap:
        "unat (off + of_nat i :: 32 word) < unat pending_cap"
        using i_lt pending_range pending_no_overflow
        by (simp add: unat_add_of_nat_index)
      show "pending +\<^sub>p uint (off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
        by (rule bufs_disjoint_uint_uintD[
          OF pending_inst pending_i_cap inst_byte_room])
    qed
    show "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
      by (rule word_sub_not_less_of_unat_add_le[OF inst_var_sum])
    show "\<forall>j<unat n.
          ptr_valid (heap_typing s)
           (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
      using inst_var_no_overflow inst_var_sum
      by (auto intro!: buf_valid_word_rangeD[OF inst_valid]
          simp: inst_var_no_overflow)
    show "\<forall>i<unat n. \<forall>j<unat n.
          i \<noteq> j \<longrightarrow>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      using inst_var_no_overflow inst_var_sum
      by (auto intro!: ptr_range_distinct_word_range_inj[OF inst_dist]
          simp: inst_var_no_overflow)
    show "\<forall>k<unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
          i < n \<longrightarrow>
          inst +\<^sub>p int k \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat (sections_t_C.inst_pos_C sec + 1)"
        and i_lt: "i < n"
      show "inst +\<^sub>p int k \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule ptr_range_distinct_word_prefix_disj[
          OF inst_dist inst_var_no_overflow inst_var_sum k_lt i_lt])
    qed
    show "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
      by (rule inst_var_no_overflow)
    show "\<forall>k<unat (sections_t_C.data_pos_C sec). \<forall>i.
          i < n \<longrightarrow>
          data +\<^sub>p int k \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat (sections_t_C.data_pos_C sec)"
        and i_lt: "i < n"
      have k_cap: "k < unat data_cap"
        using k_lt data_room by linarith
      show "data +\<^sub>p int k \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
          OF data_inst k_cap i_lt inst_var_no_overflow inst_var_sum])
    qed
    show "\<forall>k<unat (sections_t_C.addr_pos_C sec). \<forall>i.
          i < n \<longrightarrow>
          addr +\<^sub>p int k \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat (sections_t_C.addr_pos_C sec)"
        and i_lt: "i < n"
      have k_cap: "k < unat addr_cap"
        using k_lt addr_room by linarith
      have addr_inst: "bufs_disjoint addr (unat addr_cap) inst (unat inst_cap)"
        using inst_addr by (simp add: bufs_disjoint_sym)
      show "addr +\<^sub>p int k \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
          OF addr_inst k_cap i_lt inst_var_no_overflow inst_var_sum])
    qed
    show "\<forall>k<unat sz. \<forall>i.
          i < n \<longrightarrow>
          pending +\<^sub>p uint (off + of_nat k) \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat sz"
        and i_lt: "i < n"
      have pending_k_cap:
        "unat (off + of_nat k :: 32 word) < unat pending_cap"
        using k_lt pending_range pending_no_overflow
        by (simp add: unat_add_of_nat_index)
      have inst_i_cap:
        "unat (sections_t_C.inst_pos_C sec + 1 + i) < unat inst_cap"
        using i_lt inst_var_sum inst_var_no_overflow by unat_arith
      show "pending +\<^sub>p uint (off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule bufs_disjoint_uint_uintD[
          OF pending_inst pending_k_cap inst_i_cap])
    qed
    show "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
      by (rule word_sub_not_less_of_unat_add_le[OF data_room])
    show "\<forall>j<unat sz.
          ptr_valid (heap_typing s)
           (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      using data_no_overflow data_room
      by (auto intro!: buf_valid_word_rangeD[OF data_valid_buf]
          simp: data_no_overflow data_room)
    show "\<forall>j<unat sz.
          ptr_valid (heap_typing s) (pending +\<^sub>p uint (off + of_nat j))"
      using pending_no_overflow pending_range
      by (auto intro!: buf_valid_word_rangeD[OF pending_valid_buf]
          simp: pending_no_overflow pending_range)
    show "\<forall>i<unat sz. \<forall>j<unat sz.
          data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
          pending +\<^sub>p uint (off + of_nat j)"
    proof (intro allI impI)
      fix i j
      assume i_lt: "i < unat sz"
        and j_lt: "j < unat sz"
      have data_i_cap:
        "unat (sections_t_C.data_pos_C sec + of_nat i :: 32 word) <
         unat data_cap"
        using i_lt data_room data_no_overflow
        by (simp add: unat_add_of_nat_index)
      have pending_j_cap:
        "unat (off + of_nat j :: 32 word) < unat pending_cap"
        using j_lt pending_range pending_no_overflow
        by (simp add: unat_add_of_nat_index)
      have data_pending:
        "bufs_disjoint data (unat data_cap) pending (unat pending_cap)"
        using pending_data by (simp add: bufs_disjoint_sym)
      show "data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
        pending +\<^sub>p uint (off + of_nat j)"
        by (rule bufs_disjoint_uint_uintD[
          OF data_pending data_i_cap pending_j_cap])
    qed
    show "\<forall>i<unat sz. \<forall>j<unat sz.
          i \<noteq> j \<longrightarrow>
          data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
          data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
      using data_no_overflow data_room
      by (auto intro!: ptr_range_distinct_word_range_inj[OF data_dist]
          simp: data_no_overflow data_room)
    show "\<forall>k<unat (sections_t_C.data_pos_C sec). \<forall>i.
          i < sz \<longrightarrow>
          data +\<^sub>p int k \<noteq>
          data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat (sections_t_C.data_pos_C sec)"
        and i_lt: "i < sz"
      show "data +\<^sub>p int k \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
        by (rule ptr_range_distinct_word_prefix_disj[
          OF data_dist data_no_overflow data_room k_lt i_lt])
    qed
    show "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
      by (rule data_no_overflow)
    show "\<forall>k<unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
          i < sz \<longrightarrow>
          inst +\<^sub>p int k \<noteq>
          data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat (sections_t_C.inst_pos_C sec + 1)"
        and i_lt: "i < sz"
      have k_cap: "k < unat inst_cap"
        using k_lt inst_room by unat_arith
      have inst_data: "bufs_disjoint inst (unat inst_cap) data (unat data_cap)"
        using data_inst by (simp add: bufs_disjoint_sym)
      show "inst +\<^sub>p int k \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
          OF inst_data k_cap i_lt data_no_overflow data_room])
    qed
    show "\<forall>k<unat (sections_t_C.inst_pos_C sec + 1 + n). \<forall>i.
          i < sz \<longrightarrow>
          inst +\<^sub>p int k \<noteq>
          data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat (sections_t_C.inst_pos_C sec + 1 + n)"
        and i_lt: "i < sz"
      have k_cap: "k < unat inst_cap"
        using k_lt inst_var_room by linarith
      have inst_data: "bufs_disjoint inst (unat inst_cap) data (unat data_cap)"
        using data_inst by (simp add: bufs_disjoint_sym)
      show "inst +\<^sub>p int k \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
          OF inst_data k_cap i_lt data_no_overflow data_room])
    qed
    show "\<forall>k<unat (sections_t_C.addr_pos_C sec). \<forall>i.
          i < sz \<longrightarrow>
          addr +\<^sub>p int k \<noteq>
          data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat (sections_t_C.addr_pos_C sec)"
        and i_lt: "i < sz"
      have k_cap: "k < unat addr_cap"
        using k_lt addr_room by linarith
      have addr_data: "bufs_disjoint addr (unat addr_cap) data (unat data_cap)"
        using data_addr by (simp add: bufs_disjoint_sym)
      show "addr +\<^sub>p int k \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
          OF addr_data k_cap i_lt data_no_overflow data_room])
    qed
    show "\<forall>i<unat pending_frame_len.
          pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat pending_frame_len"
      have pending_i_cap:
        "unat (pending_frame_off + of_nat i :: 32 word) <
         unat pending_cap"
        using i_lt pending_frame_range pending_frame_no_overflow
        by (simp add: unat_add_of_nat_index)
      show "pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
        by (rule bufs_disjoint_uint_uintD[
          OF pending_inst pending_i_cap inst_byte_room])
    qed
    show "\<forall>k<unat pending_frame_len. \<forall>i.
          i < n \<longrightarrow>
          pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat pending_frame_len"
        and i_lt: "i < n"
      have pending_k_cap:
        "unat (pending_frame_off + of_nat k :: 32 word) <
         unat pending_cap"
        using k_lt pending_frame_range pending_frame_no_overflow
        by (simp add: unat_add_of_nat_index)
      have inst_i_cap:
        "unat (sections_t_C.inst_pos_C sec + 1 + i) < unat inst_cap"
        using i_lt inst_var_sum inst_var_no_overflow by unat_arith
      show "pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule bufs_disjoint_uint_uintD[
          OF pending_inst pending_k_cap inst_i_cap])
    qed
    show "\<forall>k<unat pending_frame_len. \<forall>i.
          i < sz \<longrightarrow>
          pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
          data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
    proof (intro allI impI)
      fix k i
      assume k_lt: "k < unat pending_frame_len"
        and i_lt: "i < sz"
      have pending_k_cap:
        "unat (pending_frame_off + of_nat k :: 32 word) <
         unat pending_cap"
        using k_lt pending_frame_range pending_frame_no_overflow
        by (simp add: unat_add_of_nat_index)
      have data_i_cap:
        "unat (sections_t_C.data_pos_C sec + i) < unat data_cap"
        using i_lt data_room data_no_overflow by unat_arith
      show "pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
        by (rule bufs_disjoint_uint_uintD[
          OF pending_data pending_k_cap data_i_cap])
    qed
  qed
qed

lemma emit_pending_run_chunk_from_loop_buffers:
  fixes s0 s :: lifted_globals
    and src tgt data inst addr pending :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap sz
        pending_frame_off pending_frame_len :: "32 word"
    and spec_src_len :: nat
  assumes buffers:
    "encode_window_loop_buffers_ok s0 src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and typing: "heap_typing s = heap_typing s0"
    and rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and pending_frame_range:
      "unat pending_frame_off + unat pending_frame_len \<le>
       unat pending_cap"
    and data_room:
      "unat (sections_t_C.data_pos_C sec) + 1 \<le> unat data_cap"
    and inst_room:
      "unat (sections_t_C.inst_pos_C sec) + 6 \<le>
       unat inst_cap"
    and addr_room:
      "unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'.
                r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK \<and>
                enc_sections_state_rel t data inst addr sec'
                  (emit_inst_spec spec_src_len
                    (RRun fill (unat sz)) spec_st)) \<and>
              heap_bytes_word t pending pending_frame_off pending_frame_len =
                heap_bytes_word s pending pending_frame_off pending_frame_len \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have inst_valid0: "buf_valid s0 inst (unat inst_cap)"
    and data_valid0: "buf_valid s0 data (unat data_cap)"
    and inst_dist: "ptr_range_distinct inst (unat inst_cap)"
    and data_dist: "ptr_range_distinct data (unat data_cap)"
    and pending_data: "bufs_disjoint pending (unat pending_cap) data (unat data_cap)"
    and pending_inst: "bufs_disjoint pending (unat pending_cap) inst (unat inst_cap)"
    and data_inst: "bufs_disjoint data (unat data_cap) inst (unat inst_cap)"
    and data_addr: "bufs_disjoint data (unat data_cap) addr (unat addr_cap)"
    and inst_addr: "bufs_disjoint inst (unat inst_cap) addr (unat addr_cap)"
    using buffers by (simp_all add: encode_window_loop_buffers_ok_def)
  have inst_valid: "buf_valid s inst (unat inst_cap)"
    and data_valid_buf: "buf_valid s data (unat data_cap)"
    using inst_valid0 data_valid0 typing by (simp_all add: buf_valid_def)
  have inst_byte_room:
    "unat (sections_t_C.inst_pos_C sec) < unat inst_cap"
    using inst_room by linarith
  have data_byte_room:
    "unat (sections_t_C.data_pos_C sec) < unat data_cap"
    using data_room by linarith
  have inst_cap32: "unat inst_cap < 2 ^ 32"
    using unat_lt2p[of inst_cap] by simp
  have pending_cap32: "unat pending_cap < 2 ^ 32"
    using unat_lt2p[of pending_cap] by simp
  have pending_frame_no_overflow:
    "unat pending_frame_off + unat pending_frame_len < 2 ^ 32"
    using pending_frame_range pending_cap32 by linarith
  have inst_byte_ptr:
    "ptr_valid (heap_typing s)
      (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
    by (rule buf_valid_uintD[OF inst_valid inst_byte_room])
  have data_byte_ptr:
    "ptr_valid (heap_typing s)
      (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
    by (rule buf_valid_uintD[OF data_valid_buf data_byte_room])
  have inst_byte_dist:
    "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
    by (rule ptr_range_distinct_mono[OF inst_dist])
       (use inst_byte_room in simp)
  have data_byte_dist:
    "ptr_range_distinct data (Suc (unat (sections_t_C.data_pos_C sec)))"
    by (rule ptr_range_distinct_mono[OF data_dist])
       (use data_byte_room in simp)
  show ?thesis
  proof (rule emit_pending_run_chunk_enc_sections_state_rel_preserves_heap_bytes_word[
      where src_len = spec_src_len, OF rel sec_ok])
    show "sections_t_C.inst_pos_C sec < inst_cap"
      using inst_byte_room by (simp add: word_less_nat_alt)
    show "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      by (rule inst_byte_ptr)
    show "ptr_range_distinct inst
          (Suc (unat (sections_t_C.inst_pos_C sec)))"
      by (rule inst_byte_dist)
    show "\<forall>i<unat (sections_t_C.data_pos_C sec).
          data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat (sections_t_C.data_pos_C sec)"
      have i_cap: "i < unat data_cap"
        using i_lt data_room by linarith
      show "data +\<^sub>p int i \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
        by (rule bufs_disjoint_int_uintD[
          OF data_inst i_cap inst_byte_room])
    qed
    show "\<forall>i<unat (sections_t_C.addr_pos_C sec).
          addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat (sections_t_C.addr_pos_C sec)"
      have i_cap: "i < unat addr_cap"
        using i_lt addr_room by linarith
      have addr_inst: "bufs_disjoint addr (unat addr_cap) inst (unat inst_cap)"
        using inst_addr by (simp add: bufs_disjoint_sym)
      show "addr +\<^sub>p int i \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
        by (rule bufs_disjoint_int_uintD[
          OF addr_inst i_cap inst_byte_room])
    qed
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
    proof -
      fix n
      assume size: "varint_size' sz s = Some n"
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_sum:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      show "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
        by (rule word_sub_not_less_of_unat_add_le[OF inst_var_sum])
    qed
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<forall>j<unat n.
           ptr_valid (heap_typing s)
            (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
    proof (intro allI impI)
      fix n j
      assume size: "varint_size' sz s = Some n"
        and j_lt: "j < unat n"
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_sum:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      have inst_var_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
        using inst_var_sum inst_cap32 by linarith
      show "ptr_valid (heap_typing s)
        (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
        by (rule buf_valid_word_rangeD[
          OF inst_valid j_lt inst_var_no_overflow inst_var_sum])
    qed
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<forall>i<unat n. \<forall>j<unat n.
          i \<noteq> j \<longrightarrow>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
    proof (intro allI impI)
      fix n i j
      assume size: "varint_size' sz s = Some n"
        and i_lt: "i < unat n"
        and j_lt: "j < unat n"
        and neq: "i \<noteq> j"
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_sum:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      have inst_var_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
        using inst_var_sum inst_cap32 by linarith
      show "inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
      proof
        assume ptr_eq:
          "inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat i) =
           inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j)"
        have "i = j"
          by (rule ptr_range_distinct_word_range_inj[
            OF inst_dist inst_var_no_overflow inst_var_sum i_lt j_lt ptr_eq])
        then show False
          using neq by simp
      qed
    qed
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<forall>k<unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
          i < n \<longrightarrow>
          inst +\<^sub>p int k \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix n k i
      assume size: "varint_size' sz s = Some n"
        and k_lt: "k < unat (sections_t_C.inst_pos_C sec + 1)"
        and i_lt: "i < n"
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_sum:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      have inst_var_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
        using inst_var_sum inst_cap32 by linarith
      show "inst +\<^sub>p int k \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule ptr_range_distinct_word_prefix_disj[
          OF inst_dist inst_var_no_overflow inst_var_sum k_lt i_lt])
    qed
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
    proof -
      fix n
      assume size: "varint_size' sz s = Some n"
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_sum:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      show "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
        using inst_var_sum inst_cap32 by linarith
    qed
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<forall>k<unat (sections_t_C.data_pos_C sec). \<forall>i.
          i < n \<longrightarrow>
          data +\<^sub>p int k \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix n k i
      assume size: "varint_size' sz s = Some n"
        and k_lt: "k < unat (sections_t_C.data_pos_C sec)"
        and i_lt: "i < n"
      have k_cap: "k < unat data_cap"
        using k_lt data_room by linarith
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_sum:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      have inst_var_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
        using inst_var_sum inst_cap32 by linarith
      show "data +\<^sub>p int k \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
          OF data_inst k_cap i_lt inst_var_no_overflow inst_var_sum])
    qed
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<forall>k<unat (sections_t_C.addr_pos_C sec). \<forall>i.
          i < n \<longrightarrow>
          addr +\<^sub>p int k \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix n k i
      assume size: "varint_size' sz s = Some n"
        and k_lt: "k < unat (sections_t_C.addr_pos_C sec)"
        and i_lt: "i < n"
      have k_cap: "k < unat addr_cap"
        using k_lt addr_room by linarith
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_sum:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      have inst_var_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
        using inst_var_sum inst_cap32 by linarith
      have addr_inst: "bufs_disjoint addr (unat addr_cap) inst (unat inst_cap)"
        using inst_addr by (simp add: bufs_disjoint_sym)
      show "addr +\<^sub>p int k \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
          OF addr_inst k_cap i_lt inst_var_no_overflow inst_var_sum])
    qed
    show "sections_t_C.data_pos_C sec < data_cap"
      using data_byte_room by (simp add: word_less_nat_alt)
    show "ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
      by (rule data_byte_ptr)
    show "ptr_range_distinct data
          (Suc (unat (sections_t_C.data_pos_C sec)))"
      by (rule data_byte_dist)
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<forall>i<unat (sections_t_C.inst_pos_C sec + 1 + n).
          inst +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
    proof (intro allI impI)
      fix n i
      assume size: "varint_size' sz s = Some n"
        and i_lt: "i < unat (sections_t_C.inst_pos_C sec + 1 + n)"
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_room:
        "unat (sections_t_C.inst_pos_C sec + 1 + n) \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      have i_cap: "i < unat inst_cap"
        using i_lt inst_var_room by linarith
      have inst_data: "bufs_disjoint inst (unat inst_cap) data (unat data_cap)"
        using data_inst by (simp add: bufs_disjoint_sym)
      show "inst +\<^sub>p int i \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
        by (rule bufs_disjoint_int_uintD[
          OF inst_data i_cap data_byte_room])
    qed
    show "\<forall>i<unat (sections_t_C.addr_pos_C sec).
          addr +\<^sub>p int i \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat (sections_t_C.addr_pos_C sec)"
      have i_cap: "i < unat addr_cap"
        using i_lt addr_room by linarith
      have addr_data: "bufs_disjoint addr (unat addr_cap) data (unat data_cap)"
        using data_addr by (simp add: bufs_disjoint_sym)
      show "addr +\<^sub>p int i \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
        by (rule bufs_disjoint_int_uintD[
          OF addr_data i_cap data_byte_room])
    qed
    show "\<forall>i<unat pending_frame_len.
          pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat pending_frame_len"
      have pending_i_cap:
        "unat (pending_frame_off + of_nat i :: 32 word) <
         unat pending_cap"
        using i_lt pending_frame_range pending_frame_no_overflow
        by (simp add: unat_add_of_nat_index)
      show "pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
        by (rule bufs_disjoint_uint_uintD[
          OF pending_inst pending_i_cap inst_byte_room])
    qed
    show "\<And>n. varint_size' sz s = Some n \<Longrightarrow>
          \<forall>k<unat pending_frame_len. \<forall>i.
          i < n \<longrightarrow>
          pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
          inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
    proof (intro allI impI)
      fix n k i
      assume size: "varint_size' sz s = Some n"
        and k_lt: "k < unat pending_frame_len"
        and i_lt: "i < n"
      have pending_k_cap:
        "unat (pending_frame_off + of_nat k :: 32 word) <
         unat pending_cap"
        using k_lt pending_frame_range pending_frame_no_overflow
        by (simp add: unat_add_of_nat_index)
      have n_le5: "unat n \<le> 5"
        by (rule varint_size'_le5[OF size])
      have inst_var_sum:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
         unat inst_cap"
        using inst_room n_le5 by unat_arith
      have inst_var_no_overflow:
        "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
        using inst_var_sum inst_cap32 by linarith
      have inst_i_cap:
        "unat (sections_t_C.inst_pos_C sec + 1 + i) < unat inst_cap"
        using i_lt inst_var_sum inst_var_no_overflow by unat_arith
      show "pending +\<^sub>p uint (pending_frame_off + of_nat k) \<noteq>
        inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
        by (rule bufs_disjoint_uint_uintD[
          OF pending_inst pending_k_cap inst_i_cap])
    qed
    show "\<forall>i<unat pending_frame_len.
          pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
          data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < unat pending_frame_len"
      have pending_i_cap:
        "unat (pending_frame_off + of_nat i :: 32 word) <
         unat pending_cap"
        using i_lt pending_frame_range pending_frame_no_overflow
        by (simp add: unat_add_of_nat_index)
      show "pending +\<^sub>p uint (pending_frame_off + of_nat i) \<noteq>
        data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
        by (rule bufs_disjoint_uint_uintD[
          OF pending_data pending_i_cap data_byte_room])
    qed
  qed
qed

lemma emit_add'_success_heap_bytes_word_cache_frame:
  assumes abs: "enc_cache_abs s c"
      and cache_wf: "enc_cache_wf c"
      and sz_ge: "(1 :: 32 word) \<le> sz"
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
              (\<exists>sec'. r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK) \<and>
              heap_bytes_word t out out_pos out_len =
                heap_bytes_word s out out_pos out_len \<and>
              enc_cache_abs t c \<and>
              enc_cache_wf c \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof (cases "sz \<le> (17 :: 32 word)")
  case True
  have frame:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec) ENC_OK) \<and>
          heap_bytes_word t out out_pos out_len =
            heap_bytes_word s out out_pos out_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_small_success_preserves_heap_bytes_word[
      OF sz_ge True sec_ok inst_byte_fits inst_byte_ptr data_fits
         data_valid pending_valid inst_byte_disj data_disj])
  have cache:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'. r = Result sec' \<and>
            enc_cache_abs t c \<and> enc_cache_wf c) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_small_success_enc_cache_abs[
      OF abs cache_wf sz_ge True inst_byte_fits inst_byte_ptr
         data_fits data_valid pending_valid])
  have combined:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1)
              (sections_t_C.addr_pos_C sec) ENC_OK) \<and>
           heap_bytes_word t out out_pos out_len =
             heap_bytes_word s out out_pos out_len \<and>
           heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'. r = Result sec' \<and>
            enc_cache_abs t c \<and> enc_cache_wf c) \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using frame cache by (simp add: runs_to_conj)
  show ?thesis
    by (rule runs_to_weaken[OF combined])
       (auto simp: sections_result_def)
next
  case False
  have large: "\<not> ((1 :: 32 word) \<le> sz \<and> sz \<le> (17 :: 32 word))"
    using False by simp
  have frame:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec) ENC_OK) \<and>
          heap_bytes_word t out out_pos out_len =
            heap_bytes_word s out out_pos out_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_large_success_preserves_heap_bytes_word[
      OF large size sec_ok inst_byte_fits inst_byte_ptr
         inst_varint_fits inst_varint_valid data_fits data_valid
         pending_valid inst_byte_disj inst_varint_disj data_disj])
  have cache:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'. r = Result sec' \<and>
            enc_cache_abs t c \<and> enc_cache_wf c) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_add'_large_success_enc_cache_abs[
      OF abs cache_wf large size inst_byte_fits inst_byte_ptr
         inst_varint_fits inst_varint_valid data_fits data_valid
         pending_valid])
  have combined:
    "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + sz)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec) ENC_OK) \<and>
           heap_bytes_word t out out_pos out_len =
             heap_bytes_word s out out_pos out_len \<and>
           heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'. r = Result sec' \<and>
            enc_cache_abs t c \<and> enc_cache_wf c) \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using frame cache by (simp add: runs_to_conj)
  show ?thesis
    by (rule runs_to_weaken[OF combined])
       (auto simp: sections_result_def)
qed

lemma emit_run'_success_heap_bytes_word_cache_frame:
  assumes abs: "enc_cache_abs s c"
      and cache_wf: "enc_cache_wf c"
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
              (\<exists>sec'. r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK) \<and>
              heap_bytes_word t out out_pos out_len =
                heap_bytes_word s out out_pos out_len \<and>
              enc_cache_abs t c \<and>
              enc_cache_wf c \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have frame:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + 1)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec) ENC_OK) \<and>
          heap_bytes_word t out out_pos out_len =
            heap_bytes_word s out out_pos out_len \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_run'_success_preserves_heap_bytes_word[
      OF size sec_ok inst_byte_fits inst_byte_ptr inst_varint_fits
         inst_varint_valid data_byte_fits data_byte_ptr inst_byte_disj
         inst_varint_disj data_byte_disj])
  have cache:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          (\<exists>sec'. r = Result sec' \<and>
            enc_cache_abs t c \<and> enc_cache_wf c) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_run'_success_enc_cache_abs[
      OF abs cache_wf size inst_byte_fits inst_byte_ptr
         inst_varint_fits inst_varint_valid data_byte_fits data_byte_ptr])
  have combined:
    "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
       \<lbrace> \<lambda>r t.
          ((\<exists>sec'.
            r = Result sec' \<and>
            sections_result sec'
              (sections_t_C.data_pos_C sec + 1)
              (sections_t_C.inst_pos_C sec + 1 + n)
              (sections_t_C.addr_pos_C sec) ENC_OK) \<and>
           heap_bytes_word t out out_pos out_len =
             heap_bytes_word s out out_pos out_len \<and>
           heap_typing t = heap_typing s) \<and>
          ((\<exists>sec'. r = Result sec' \<and>
            enc_cache_abs t c \<and> enc_cache_wf c) \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using frame cache by (simp add: runs_to_conj)
  show ?thesis
    by (rule runs_to_weaken[OF combined])
       (auto simp: sections_result_def)
qed

lemma emit_add'_loop_buffers_heap_word_cache_frame:
  fixes s0 s :: lifted_globals
    and src tgt data inst addr pending out :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap off sz
        out_len :: "32 word"
  assumes buffers:
    "encode_window_loop_buffers_ok s0 src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and typing: "heap_typing s = heap_typing s0"
    and abs: "enc_cache_abs s c"
    and cache_wf: "enc_cache_wf c"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and sz_ge: "(1 :: 32 word) \<le> sz"
    and pending_range: "unat off + unat sz \<le> unat pending_cap"
    and data_room:
      "unat (sections_t_C.data_pos_C sec) + unat sz \<le>
       unat data_cap"
    and inst_room:
      "unat (sections_t_C.inst_pos_C sec) + 6 \<le>
       unat inst_cap"
    and out_inst: "bufs_disjoint out (unat out_len) inst (unat inst_cap)"
    and out_data: "bufs_disjoint out (unat out_len) data (unat data_cap)"
  shows "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'. r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK) \<and>
              heap_bytes_word t out 0 out_len =
                heap_bytes_word s out 0 out_len \<and>
              enc_cache_abs t c \<and>
              enc_cache_wf c \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  obtain n where size: "varint_size' sz s = Some n"
    using varint_size'_some by blast
  have n_le5: "unat n \<le> 5"
    by (rule varint_size'_le5[OF size])
  have inst_valid0: "buf_valid s0 inst (unat inst_cap)"
    and data_valid0: "buf_valid s0 data (unat data_cap)"
    and pending_valid0: "buf_valid s0 pending (unat pending_cap)"
    using buffers by (simp_all add: encode_window_loop_buffers_ok_def)
  have inst_valid: "buf_valid s inst (unat inst_cap)"
    and data_valid_buf: "buf_valid s data (unat data_cap)"
    and pending_valid_buf: "buf_valid s pending (unat pending_cap)"
    using inst_valid0 data_valid0 pending_valid0 typing
    by (simp_all add: buf_valid_def)
  have inst_byte_room:
    "unat (sections_t_C.inst_pos_C sec) < unat inst_cap"
    using inst_room by linarith
  have inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
    using inst_byte_room by (simp add: word_less_nat_alt)
  have inst_byte_ptr:
    "ptr_valid (heap_typing s)
      (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
    by (rule buf_valid_uintD[OF inst_valid inst_byte_room])
  have inst_cap32: "unat inst_cap < 2 ^ 32"
    using unat_lt2p[of inst_cap] by simp
  have data_cap32: "unat data_cap < 2 ^ 32"
    using unat_lt2p[of data_cap] by simp
  have pending_cap32: "unat pending_cap < 2 ^ 32"
    using unat_lt2p[of pending_cap] by simp
  have data_no_overflow:
    "unat (sections_t_C.data_pos_C sec) + unat sz < 2 ^ 32"
    using data_room data_cap32 by linarith
  have pending_no_overflow:
    "unat off + unat sz < 2 ^ 32"
    using pending_range pending_cap32 by linarith
  have inst_var_sum:
    "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
     unat inst_cap"
    using inst_room n_le5 by unat_arith
  have inst_var_no_overflow:
    "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
    using inst_var_sum inst_cap32 by linarith
  have inst_varint_fits:
    "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
    by (rule word_sub_not_less_of_unat_add_le[OF inst_var_sum])
  have inst_varint_valid: "\<forall>j < unat n.
    ptr_valid (heap_typing s)
      (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
    using inst_var_no_overflow inst_var_sum
    by (auto intro!: buf_valid_word_rangeD[OF inst_valid]
        simp: inst_var_no_overflow)
  have data_fits:
    "\<not> data_cap - sections_t_C.data_pos_C sec < sz"
    by (rule word_sub_not_less_of_unat_add_le[OF data_room])
  have data_valid: "\<forall>j < unat sz.
    ptr_valid (heap_typing s)
      (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
    using data_no_overflow data_room
    by (auto intro!: buf_valid_word_rangeD[OF data_valid_buf]
        simp: data_no_overflow)
  have pending_valid: "\<forall>j < unat sz.
    ptr_valid (heap_typing s) (pending +\<^sub>p uint (off + of_nat j))"
    using pending_no_overflow pending_range
    by (auto intro!: buf_valid_word_rangeD[OF pending_valid_buf]
        simp: pending_no_overflow)
  have out_no_overflow: "0 + unat out_len < 2 ^ 32"
    using unat_lt2p[of out_len] by simp
  have out_range: "0 + unat out_len \<le> unat out_len"
    by simp
  have inst_byte_disj: "\<forall>i < unat out_len.
    out +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
    inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < unat out_len"
    have disj_int:
      "out +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
       inst +\<^sub>p int (unat (sections_t_C.inst_pos_C sec))"
      apply (rule bufs_disjoint_word_range_leftD[
        where pos = "0 :: 32 word" and len = out_len
          and k = "unat (sections_t_C.inst_pos_C sec)"])
          apply (rule out_inst)
         apply (rule i_lt)
        using out_no_overflow apply simp
       using out_range apply simp
      apply (rule inst_byte_room)
      done
    have inst_ptr_eq:
      "inst +\<^sub>p uint (sections_t_C.inst_pos_C sec) =
       inst +\<^sub>p int (unat (sections_t_C.inst_pos_C sec))"
      by (simp only: uint_nat)
    show "out +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
      inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      apply (subst inst_ptr_eq)
      apply (rule disj_int)
      done
  qed
  have inst_varint_disj: "\<forall>k < unat out_len. \<forall>i.
    i < n \<longrightarrow>
    out +\<^sub>p uint ((0 :: 32 word) + of_nat k) \<noteq>
    inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < unat out_len"
      and i_lt: "i < n"
    have out_k:
      "out +\<^sub>p uint ((0 :: 32 word) + of_nat k) = out +\<^sub>p int k"
      using k_lt unat_lt2p[of out_len]
      by (simp add: unat_of_nat_eq uint_nat)
    have disj_int:
      "out +\<^sub>p int k \<noteq>
       inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
        OF out_inst k_lt i_lt inst_var_no_overflow inst_var_sum])
    show "out +\<^sub>p uint ((0 :: 32 word) + of_nat k) \<noteq>
      inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      using out_k disj_int by simp
  qed
  have data_disj: "\<forall>k < unat out_len. \<forall>i.
    i < sz \<longrightarrow>
    out +\<^sub>p uint ((0 :: 32 word) + of_nat k) \<noteq>
    data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < unat out_len"
      and i_lt: "i < sz"
    have out_k:
      "out +\<^sub>p uint ((0 :: 32 word) + of_nat k) = out +\<^sub>p int k"
      using k_lt unat_lt2p[of out_len]
      by (simp add: unat_of_nat_eq uint_nat)
    have disj_int:
      "out +\<^sub>p int k \<noteq>
       data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
        OF out_data k_lt i_lt data_no_overflow data_room])
    show "out +\<^sub>p uint ((0 :: 32 word) + of_nat k) \<noteq>
      data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      using out_k disj_int by simp
  qed
  show ?thesis
    by (rule emit_add'_success_heap_bytes_word_cache_frame[
      where n = n, OF abs cache_wf sz_ge size sec_ok inst_byte_fits
        inst_byte_ptr inst_varint_fits inst_varint_valid data_fits
        data_valid pending_valid inst_byte_disj inst_varint_disj data_disj])
qed

lemma emit_run'_loop_buffers_heap_word_cache_frame:
  fixes s0 s :: lifted_globals
    and src tgt data inst addr pending out :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap sz out_len ::
      "32 word"
  assumes buffers:
    "encode_window_loop_buffers_ok s0 src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and typing: "heap_typing s = heap_typing s0"
    and abs: "enc_cache_abs s c"
    and cache_wf: "enc_cache_wf c"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and data_room:
      "unat (sections_t_C.data_pos_C sec) + 1 \<le> unat data_cap"
    and inst_room:
      "unat (sections_t_C.inst_pos_C sec) + 6 \<le>
       unat inst_cap"
    and out_inst: "bufs_disjoint out (unat out_len) inst (unat inst_cap)"
    and out_data: "bufs_disjoint out (unat out_len) data (unat data_cap)"
  shows "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>sec'. r = Result sec' \<and>
                sections_t_C.err_C sec' = ENC_OK) \<and>
              heap_bytes_word t out 0 out_len =
                heap_bytes_word s out 0 out_len \<and>
              enc_cache_abs t c \<and>
              enc_cache_wf c \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  obtain n where size: "varint_size' sz s = Some n"
    using varint_size'_some by blast
  have n_le5: "unat n \<le> 5"
    by (rule varint_size'_le5[OF size])
  have inst_valid0: "buf_valid s0 inst (unat inst_cap)"
    and data_valid0: "buf_valid s0 data (unat data_cap)"
    using buffers by (simp_all add: encode_window_loop_buffers_ok_def)
  have inst_valid: "buf_valid s inst (unat inst_cap)"
    and data_valid_buf: "buf_valid s data (unat data_cap)"
    using inst_valid0 data_valid0 typing by (simp_all add: buf_valid_def)
  have inst_byte_room:
    "unat (sections_t_C.inst_pos_C sec) < unat inst_cap"
    using inst_room by linarith
  have data_byte_room:
    "unat (sections_t_C.data_pos_C sec) < unat data_cap"
    using data_room by linarith
  have inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
    using inst_byte_room by (simp add: word_less_nat_alt)
  have data_byte_fits: "sections_t_C.data_pos_C sec < data_cap"
    using data_byte_room by (simp add: word_less_nat_alt)
  have inst_byte_ptr:
    "ptr_valid (heap_typing s)
      (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
    by (rule buf_valid_uintD[OF inst_valid inst_byte_room])
  have data_byte_ptr:
    "ptr_valid (heap_typing s)
      (data +\<^sub>p uint (sections_t_C.data_pos_C sec))"
    by (rule buf_valid_uintD[OF data_valid_buf data_byte_room])
  have inst_cap32: "unat inst_cap < 2 ^ 32"
    using unat_lt2p[of inst_cap] by simp
  have inst_var_sum:
    "unat (sections_t_C.inst_pos_C sec + 1) + unat n \<le>
     unat inst_cap"
    using inst_room n_le5 by unat_arith
  have inst_var_no_overflow:
    "unat (sections_t_C.inst_pos_C sec + 1) + unat n < 2 ^ 32"
    using inst_var_sum inst_cap32 by linarith
  have inst_varint_fits:
    "\<not> inst_cap - (sections_t_C.inst_pos_C sec + 1) < n"
    by (rule word_sub_not_less_of_unat_add_le[OF inst_var_sum])
  have inst_varint_valid: "\<forall>j < unat n.
    ptr_valid (heap_typing s)
      (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + of_nat j))"
    using inst_var_no_overflow inst_var_sum
    by (auto intro!: buf_valid_word_rangeD[OF inst_valid]
        simp: inst_var_no_overflow)
  have out_no_overflow: "0 + unat out_len < 2 ^ 32"
    using unat_lt2p[of out_len] by simp
  have out_range: "0 + unat out_len \<le> unat out_len"
    by simp
  have inst_byte_disj: "\<forall>i < unat out_len.
    out +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
    inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < unat out_len"
    have disj_int:
      "out +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
       inst +\<^sub>p int (unat (sections_t_C.inst_pos_C sec))"
      apply (rule bufs_disjoint_word_range_leftD[
        where pos = "0 :: 32 word" and len = out_len
          and k = "unat (sections_t_C.inst_pos_C sec)"])
          apply (rule out_inst)
         apply (rule i_lt)
        using out_no_overflow apply simp
       using out_range apply simp
      apply (rule inst_byte_room)
      done
    have inst_ptr_eq:
      "inst +\<^sub>p uint (sections_t_C.inst_pos_C sec) =
       inst +\<^sub>p int (unat (sections_t_C.inst_pos_C sec))"
      by (simp only: uint_nat)
    show "out +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
      inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      apply (subst inst_ptr_eq)
      apply (rule disj_int)
      done
  qed
  have inst_varint_disj: "\<forall>k < unat out_len. \<forall>i.
    i < n \<longrightarrow>
    out +\<^sub>p uint ((0 :: 32 word) + of_nat k) \<noteq>
    inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < unat out_len"
      and i_lt: "i < n"
    have out_k:
      "out +\<^sub>p uint ((0 :: 32 word) + of_nat k) = out +\<^sub>p int k"
      using k_lt unat_lt2p[of out_len]
      by (simp add: unat_of_nat_eq uint_nat)
    have disj_int:
      "out +\<^sub>p int k \<noteq>
       inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
        OF out_inst k_lt i_lt inst_var_no_overflow inst_var_sum])
    show "out +\<^sub>p uint ((0 :: 32 word) + of_nat k) \<noteq>
      inst +\<^sub>p uint (sections_t_C.inst_pos_C sec + 1 + i)"
      using out_k disj_int by simp
  qed
  have data_byte_disj: "\<forall>i < unat out_len.
    out +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
    data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < unat out_len"
    have out_i:
      "out +\<^sub>p uint ((0 :: 32 word) + of_nat i) = out +\<^sub>p int i"
      using i_lt unat_lt2p[of out_len]
      by (simp add: unat_of_nat_eq uint_nat)
    have disj_int:
      "out +\<^sub>p int i \<noteq>
       data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      by (rule bufs_disjoint_int_uintD[
        OF out_data i_lt data_byte_room])
    show "out +\<^sub>p uint ((0 :: 32 word) + of_nat i) \<noteq>
      data +\<^sub>p uint (sections_t_C.data_pos_C sec)"
      using out_i disj_int by simp
  qed
  show ?thesis
    by (rule emit_run'_success_heap_bytes_word_cache_frame[
      where n = n, OF abs cache_wf size sec_ok inst_byte_fits
        inst_byte_ptr inst_varint_fits inst_varint_valid data_byte_fits
        data_byte_ptr inst_byte_disj inst_varint_disj data_byte_disj])
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

lemma near_reset_loop_preserves_encoder_index_post:
  assumes index:
    "encoder_index_post s0 s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
  shows "(whileLoop (\<lambda>idx st. idx < (4 :: 32 word))
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word) \<and>
          encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
            src_bytes tgt_bytes \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 4 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 4 \<and>
              encoder_index_post s0 st src src_len tgt tgt_len head_arr
                next_arr src_bytes tgt_bytes"])
  subgoal by simp
  subgoal using index by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (auto simp: word_less_nat_alt unat_word_ariths(1)
      encoder_index_post_def source_index_heap_rel_def
      source_index_heap_nexts_wf_def source_index_heap_chains_closed_def
      heap_w32_list_def)
    done
  done

lemma same_reset_loop_preserves_encoder_index_post:
  assumes index:
    "encoder_index_post s0 s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
  shows "(whileLoop (\<lambda>idx st. idx < (0x300 :: 32 word))
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
    \<lbrace> \<lambda>r t. r = Result (0x300 :: 32 word) \<and>
          encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
            src_bytes tgt_bytes \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 768 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 768 \<and>
              encoder_index_post s0 st src src_len tgt tgt_len head_arr
                next_arr src_bytes tgt_bytes"])
  subgoal by simp
  subgoal using index by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (auto simp: word_less_nat_alt unat_word_ariths(1)
      encoder_index_post_def source_index_heap_rel_def
      source_index_heap_nexts_wf_def source_index_heap_chains_closed_def
      heap_w32_list_def)
    done
  done

lemma cache_reset'_preserves_encoder_index_post:
  assumes index:
    "encoder_index_post s0 s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
  shows "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
          encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
            src_bytes tgt_bytes \<rbrace>"
  unfolding cache_reset'_def
  supply near_reset_loop_preserves_encoder_index_post[runs_to_vcg]
  supply same_reset_loop_preserves_encoder_index_post[runs_to_vcg]
  apply runs_to_vcg
  using index
  by (auto simp: encoder_index_post_def source_index_heap_rel_def
      source_index_heap_nexts_wf_def source_index_heap_chains_closed_def
      heap_w32_list_def)

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

definition encoder_final_section_caps_ok ::
  "byte list \<Rightarrow> byte list \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> bool" where
  "encoder_final_section_caps_ok src_bytes tgt_bytes
      data_cap inst_cap addr_cap \<longleftrightarrow>
     length (enc_data (encode_window_final_spec_state src_bytes tgt_bytes))
       \<le> unat data_cap \<and>
     length (enc_inst (encode_window_final_spec_state src_bytes tgt_bytes))
       \<le> unat inst_cap \<and>
     length (enc_addr (encode_window_final_spec_state src_bytes tgt_bytes))
       \<le> unat addr_cap"

definition encode_window_spec_reaches_final ::
  "byte list \<Rightarrow> byte list \<Rightarrow> enc_full_state \<Rightarrow> bool" where
  "encode_window_spec_reaches_final src_bytes tgt_bytes spec_st \<longleftrightarrow>
     encode_window_full_loop (length tgt_bytes + 1 - enc_tp spec_st)
       src_bytes tgt_bytes (build_index_spec src_bytes) spec_st =
       encode_window_final_spec_state src_bytes tgt_bytes"

definition encode_window_section_prefix_budget ::
  "byte list \<Rightarrow> byte list \<Rightarrow> enc_full_state \<Rightarrow> bool" where
  "encode_window_section_prefix_budget src_bytes tgt_bytes spec_st \<longleftrightarrow>
     length (enc_data spec_st) \<le>
       length (enc_data (encode_window_final_spec_state src_bytes tgt_bytes)) \<and>
     length (enc_inst spec_st) \<le>
       length (enc_inst (encode_window_final_spec_state src_bytes tgt_bytes)) \<and>
     length (enc_addr spec_st) \<le>
       length (enc_addr (encode_window_final_spec_state src_bytes tgt_bytes))"

definition encode_window_section_budget ::
  "byte list \<Rightarrow> byte list \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   enc_full_state \<Rightarrow> bool" where
  "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap spec_st \<longleftrightarrow>
     encode_window_spec_reaches_final src_bytes tgt_bytes spec_st \<and>
     encode_window_section_prefix_budget src_bytes tgt_bytes spec_st \<and>
     encoder_final_section_caps_ok src_bytes tgt_bytes
       data_cap inst_cap addr_cap"

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
     unat tp \<le> unat tgt_len \<and>
     unat pend_len \<le> unat pending_cap \<and>
     unat (sections_t_C.data_pos_C sec) \<le> unat data_cap \<and>
     unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap \<and>
     unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap \<and>
     unat (sections_t_C.data_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat data_cap \<and>
     unat (sections_t_C.inst_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat inst_cap \<and>
     unat (sections_t_C.addr_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat addr_cap \<and>
     enc_cache_abs s (enc_cache spec_st) \<and>
     enc_cache_wf (enc_cache spec_st)"

definition encode_window_loop_budget_rel ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   sections_t_C \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> enc_full_state \<Rightarrow> bool" where
  "encode_window_loop_budget_rel s src src_len tgt tgt_len
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
     unat tp \<le> unat tgt_len \<and>
     unat pend_len \<le> unat pending_cap \<and>
     unat (sections_t_C.data_pos_C sec) \<le> unat data_cap \<and>
     unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap \<and>
     unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap \<and>
     unat (sections_t_C.data_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat data_cap \<and>
     unat (sections_t_C.inst_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat inst_cap \<and>
     encode_window_section_budget src_bytes tgt_bytes
       data_cap inst_cap addr_cap spec_st \<and>
     enc_cache_abs s (enc_cache spec_st) \<and>
     enc_cache_wf (enc_cache spec_st)"

lemma encode_window_loop_rel_zero_pending_witness:
  assumes src_heap: "heap_bytes s src (unat src_len) = src_bytes"
      and tgt_heap: "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
      and src_len_eq: "length src_bytes = unat src_len"
      and tgt_len_eq: "length tgt_bytes = unat tgt_len"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and tp_le: "unat tp \<le> unat tgt_len"
      and data_pos: "unat (sections_t_C.data_pos_C sec) \<le> unat data_cap"
      and inst_pos: "unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap"
      and addr_pos: "unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"
      and data_room:
        "unat (sections_t_C.data_pos_C sec) + (unat tgt_len - unat tp) + 64
          \<le> unat data_cap"
      and inst_room:
        "unat (sections_t_C.inst_pos_C sec) + (unat tgt_len - unat tp) + 64
          \<le> unat inst_cap"
      and addr_room:
        "unat (sections_t_C.addr_pos_C sec) + (unat tgt_len - unat tp) + 64
          \<le> unat addr_cap"
      and cache_abs: "enc_cache_abs s c"
      and cache_wf: "enc_cache_wf c"
  shows "\<exists>spec_st. encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp 0 src_bytes tgt_bytes spec_st"
proof -
  let ?spec =
    "\<lparr> enc_tp = unat tp,
       enc_flushed = unat tp,
       enc_pending = [],
       enc_data = heap_bytes s data (unat (sections_t_C.data_pos_C sec)),
       enc_inst = heap_bytes s inst (unat (sections_t_C.inst_pos_C sec)),
       enc_addr = heap_bytes s addr (unat (sections_t_C.addr_pos_C sec)),
       enc_cache = c,
       enc_trace = [] \<rparr>"
  show ?thesis
    apply (rule exI[where x = ?spec])
    using src_heap tgt_heap src_len_eq tgt_len_eq sec_ok tp_le
      data_pos inst_pos addr_pos data_room inst_room addr_room
      cache_abs cache_wf
    by (auto simp: encode_window_loop_rel_def enc_sections_state_rel_def
                   emitted_sections_def heap_bytes_word_def)
qed

lemma write_byte'_success_preserves_heap_bytes2_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and disj1: "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
      and disj2: "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   enc_cache_abs t c \<and>
                   enc_cache_wf c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have h1:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_success_preserves_heap_bytes
      [OF pos_lt ptr_ok disj1])
  have h2:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_success_preserves_heap_bytes
      [OF pos_lt ptr_ok disj2])
  have cache:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               enc_cache_abs t c \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_success_preserves_enc_cache_abs
      [OF abs pos_lt ptr_ok])
  have h12:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using h1 h2 by (simp add: runs_to_conj)
  have combined:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t.
          ((r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
            heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
            heap_typing t = heap_typing s) \<and>
           (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
            heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
            heap_typing t = heap_typing s)) \<and>
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           enc_cache_abs t c \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using h12 cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    using wf by auto
qed

lemma write_bytes'_success_preserves_heap_bytes2_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and fits: "\<not> cap - pos < len"
      and dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
      and disj1: "\<forall>k < out1_n. \<forall>i.
           i < len \<longrightarrow> out1 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and disj2: "\<forall>k < out2_n. \<forall>i.
           i < len \<longrightarrow> out2 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   enc_cache_abs t c \<and>
                   enc_cache_wf c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have h1:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_preserves_heap_bytes
      [OF fits dst_valid src_valid disj1])
  have h2:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_preserves_heap_bytes
      [OF fits dst_valid src_valid disj2])
  have cache:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               enc_cache_abs t c \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_preserves_enc_cache_abs
      [OF abs fits dst_valid src_valid])
  have h12:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using h1 h2 by (simp add: runs_to_conj)
  have combined:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t.
          ((r = Result (wr_t_C (pos + len) ENC_OK) \<and>
            heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
            heap_typing t = heap_typing s) \<and>
           (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
            heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
            heap_typing t = heap_typing s)) \<and>
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           enc_cache_abs t c \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using h12 cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    using wf by auto
qed

lemma write_varint'_success_preserves_heap_bytes2_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and disj1: "\<forall>k < out1_n. \<forall>i.
           i < n \<longrightarrow> out1 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and disj2: "\<forall>k < out2_n. \<forall>i.
           i < n \<longrightarrow> out2 +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   enc_cache_abs t c \<and>
                   enc_cache_wf c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have h1:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes_bounded
      [OF size fits dst_valid disj1])
  have h2:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes_bounded
      [OF size fits dst_valid disj2])
  have cache:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               enc_cache_abs t c \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_enc_cache_abs_bounded
      [OF abs size fits dst_valid])
  have h12:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using h1 h2 by (simp add: runs_to_conj)
  have combined:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t.
          ((r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
            heap_typing t = heap_typing s) \<and>
           (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
            heap_typing t = heap_typing s)) \<and>
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           enc_cache_abs t c \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using h12 cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    using wf by auto
qed

lemma emit_address'_success_byte_preserves_heap_bytes2_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
      and pos_lt: "addr_pos < addr_cap"
      and ptr_ok: "ptr_valid (heap_typing s) (addr_buf +\<^sub>p uint addr_pos)"
      and dist: "ptr_range_distinct addr_buf (Suc (unat addr_pos))"
      and disj1: "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint addr_pos"
      and disj2: "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint addr_pos"
  shows "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   enc_cache_abs t c \<and>
                   enc_cache_wf c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have heaps:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule runs_to_weaken[
      OF emit_address'_success_byte_heap_bytes_append_preserves2
        [OF mode_ge pos_lt ptr_ok dist disj1 disj2]])
    by auto
  have cache:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
               enc_cache_abs t c \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_address'_success_byte_preserves_enc_cache_abs
      [OF abs mode_ge pos_lt ptr_ok])
  have combined:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
           enc_cache_abs t c \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using heaps cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    using wf by auto
qed

lemma emit_address'_success_varint_preserves_heap_bytes2_cache_abs:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and mode_lt: "mode_t_C.mode_C m < (6 :: 32 word)"
      and size: "varint_size' (mode_t_C.arg_C m) s = Some n"
      and fits: "\<not> addr_cap - addr_pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s)
             (addr_buf +\<^sub>p uint (addr_pos + of_nat j))"
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
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   enc_cache_abs t c \<and>
                   enc_cache_wf c \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have heaps:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule runs_to_weaken[
      OF emit_address'_success_varint_heap_bytes_append_preserves2
        [OF mode_lt size fits dst_valid dst_inj prefix_disj no_overflow
            disj1 disj2]])
    by auto
  have cache:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
               enc_cache_abs t c \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_address'_success_varint_preserves_enc_cache_abs
      [OF abs mode_lt size fits dst_valid])
  have combined:
    "emit_address' addr_buf addr_cap addr_pos m \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
           enc_cache_abs t c \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using heaps cache by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    using wf by auto
qed

lemma cache_update'_preserves_heap_bytes2_enc_cache_abs_wf:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
  shows "cache_update' addr \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   enc_cache_abs t (cache_update c (unat addr)) \<and>
                   enc_cache_wf (cache_update c (unat addr)) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have h1_cache:
    "cache_update' addr \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
               enc_cache_abs t (cache_update c (unat addr)) \<and>
               enc_cache_wf (cache_update c (unat addr)) \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<rbrace>"
    by (rule cache_update'_enc_cache_abs_wf[OF abs wf])
  have h2:
    "cache_update' addr \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<rbrace>"
    apply (rule cache_update'_preserves_heap_bytes)
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have combined:
    "cache_update' addr \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result () \<and>
           enc_cache_abs t (cache_update c (unat addr)) \<and>
           enc_cache_wf (cache_update c (unat addr)) \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n) \<and>
          (r = Result () \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n) \<rbrace>"
    using h1_cache h2 by (simp add: runs_to_conj)
  show ?thesis
	    apply (rule runs_to_weaken[OF combined])
	    by auto
qed

lemma try_emit_add_copy'_mode_gt5_success_heap_bytes2_cache_frame:
  fixes op pend_len :: "32 word"
    and m
  defines "op \<equiv>
    (235 + (mode_t_C.mode_C m - 6) * 4 + (pend_len - 1) :: 32 word)"
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_eq: "copy_len = (4 :: 32 word)"
      and mode_gt: "(5 :: 32 word) < mode_t_C.mode_C m"
      and mode_le: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_byte_fits: "sections_t_C.inst_pos_C sec < inst_cap"
      and inst_byte_ptr:
        "ptr_valid (heap_typing s)
          (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
      and inst_out1_disj:
        "\<forall>i < out1_n.
           out1 +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and inst_out2_disj:
        "\<forall>i < out2_n.
           out2 +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
      and data_fits:
        "\<not> data_cap - sections_t_C.data_pos_C sec < pend_len"
      and data_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
      and pending_valid: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s)
          (pending +\<^sub>p uint (of_nat j :: 32 word))"
      and data_out1_disj: "\<forall>k < out1_n. \<forall>i.
        i < pend_len \<longrightarrow>
        out1 +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and data_out2_disj: "\<forall>k < out2_n. \<forall>i.
        i < pend_len \<longrightarrow>
        out2 +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
      and addr_byte_fits: "sections_t_C.addr_pos_C sec < addr_cap"
      and addr_byte_ptr:
        "ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
      and addr_byte_dist:
        "ptr_range_distinct addr_buf (Suc (unat (sections_t_C.addr_pos_C sec)))"
      and addr_out1_disj:
        "\<forall>i < out1_n.
           out1 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
      and addr_out2_disj:
        "\<forall>i < out2_n.
           out2 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.fused_C f = copy_len \<and>
                heap_bytes t out1 out1_n =
                  heap_bytes s out1 out1_n \<and>
                heap_bytes t out2 out2_n =
                  heap_bytes s out2 out2_n \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have op_nz:
    "(0xD2 + (mode_t_C.mode_C m * 4 + pend_len) :: 32 word) \<noteq> 0"
    using pend_ge pend_le mode_gt mode_le
    by (auto simp: word_less_nat_alt word_le_nat_alt
                   word_neq_0_conv unat_word_ariths)
  have mode_ge: "\<not> mode_t_C.mode_C m < (6 :: 32 word)"
    using mode_gt by (simp add: word_less_nat_alt)
  note gets_the_best_mode'_result[runs_to_vcg]
  note add_copy_opcode'_mode_gt5[runs_to_vcg]
  show ?thesis
    unfolding try_emit_add_copy'_def op_def
    using bm pend_ge pend_le copy_eq mode_gt mode_le sec_ok
    apply runs_to_vcg
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt word_le_nat_alt
                         word_neq_0_conv unat_word_ariths)
    using op_nz apply simp
        apply (rule runs_to_weaken[
          OF write_byte'_success_preserves_heap_bytes2_cache_abs])
             apply (rule abs)
            apply (rule cache_wf)
           apply (rule inst_byte_fits)
          apply (rule inst_byte_ptr)
         apply (rule inst_out1_disj)
        apply (rule inst_out2_disj)
       apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[
         OF write_bytes'_success_preserves_heap_bytes2_cache_abs])
              apply assumption
             apply assumption
            apply (rule data_fits)
           apply clarsimp
           using data_valid apply blast
          apply clarsimp
          using pending_valid apply blast
         apply (rule data_out1_disj)
        apply (rule data_out2_disj)
       apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[
         OF emit_address'_success_byte_preserves_heap_bytes2_cache_abs])
              apply assumption
             apply assumption
            apply (rule mode_ge)
           apply (rule addr_byte_fits)
          apply (simp add: addr_byte_ptr)
         apply (rule addr_byte_dist)
        apply (rule addr_out1_disj)
       apply (rule addr_out2_disj)
      apply clarsimp
	      apply runs_to_vcg
	      apply (rule runs_to_weaken[
	        OF cache_update'_preserves_heap_bytes2_enc_cache_abs_wf[
	          of _ _ _ out1 out1_n out2 out2_n]])
       apply assumption
      apply assumption
    using copy_eq by auto
qed

lemma emit_copy'_pack_heap_bytes2_cache_frame:
  assumes frame_cache:
    "((\<exists>sec'.
         r = Result sec' \<and>
         sections_result sec' data_pos inst_pos' addr_pos' ENC_OK \<and>
         heap1 \<and> heap2 \<and> typing) \<and>
      ((\<exists>sec'.
         r = Result sec' \<and> cache_abs \<and> cache_wf) \<and> typing))"
      and inst_pos': "inst_pos' = inst_pos + inst_inc"
      and addr_pos': "addr_pos' = addr_pos + addr_inc"
      and inst_inc: "unat inst_inc \<le> 6"
      and addr_inc: "unat addr_inc \<le> 5"
      and addr_inc_payload: "unat addr_inc \<le> addr_payload_bound"
  shows "\<exists>sec' inst_inc' addr_inc'.
      r = Result sec' \<and>
      sections_result sec' data_pos (inst_pos + inst_inc')
        (addr_pos + addr_inc') ENC_OK \<and>
      unat inst_inc' \<le> 6 \<and>
      unat addr_inc' \<le> 5 \<and>
      unat addr_inc' \<le> addr_payload_bound \<and>
      heap1 \<and> heap2 \<and> cache_abs \<and> cache_wf \<and> typing"
proof -
  obtain sec' where
      r: "r = Result sec'"
      and sec_res:
        "sections_result sec' data_pos inst_pos' addr_pos' ENC_OK"
      and heap1 and heap2 and typing
    using frame_cache by blast
  moreover have cache_abs and cache_wf
    using frame_cache by blast+
  ultimately show ?thesis
    using inst_pos' addr_pos' inst_inc addr_inc addr_inc_payload
    by (intro exI[where x = sec'] exI[where x = inst_inc]
        exI[where x = addr_inc] conjI)
      simp_all
qed

lemma emit_copy'_success_heap_bytes2_cache_frame_bounded:
  assumes abs: "enc_cache_abs s c"
      and wf: "enc_cache_wf c"
      and bm: "best_mode' copy_addr here s = Some m"
      and mode_le8: "mode_t_C.mode_C m \<le> (8 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
      and copy_size: "varint_size' copy_len s = Some sn"
      and sec_ok: "sections_t_C.err_C sec = ENC_OK"
      and inst_valid: "buf_valid s inst (unat inst_cap)"
      and addr_valid: "buf_valid s addr_buf (unat addr_cap)"
      and inst_dist: "ptr_range_distinct inst (unat inst_cap)"
      and addr_dist: "ptr_range_distinct addr_buf (unat addr_cap)"
      and out1_inst_disj: "bufs_disjoint out1 out1_n inst (unat inst_cap)"
      and out2_inst_disj: "bufs_disjoint out2 out2_n inst (unat inst_cap)"
      and out1_addr_disj: "bufs_disjoint out1 out1_n addr_buf (unat addr_cap)"
      and out2_addr_disj: "bufs_disjoint out2 out2_n addr_buf (unat addr_cap)"
      and inst_room:
        "unat (sections_t_C.inst_pos_C sec) + 6 \<le> unat inst_cap"
      and addr_room:
        "unat (sections_t_C.addr_pos_C sec) + 5 \<le> unat addr_cap"
  shows "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
            \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' inst_inc addr_inc.
              r = Result sec' \<and>
	              sections_result sec'
	                (sections_t_C.data_pos_C sec)
	                (sections_t_C.inst_pos_C sec + inst_inc)
	                (sections_t_C.addr_pos_C sec + addr_inc)
	                ENC_OK \<and>
	              unat inst_inc \<le> 6 \<and>
	              unat addr_inc \<le> 5 \<and>
	              unat addr_inc \<le>
	                (if mode_t_C.mode_C m < (6 :: 32 word)
	                 then unat an else 1) \<and>
	              heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
	              heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
              enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
              enc_cache_wf (cache_update c (unat copy_addr)) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have an_le5: "unat an \<le> 5"
    by (rule varint_size'_le5[OF addr_size])
  have sn_le5: "unat sn \<le> 5"
    by (rule varint_size'_le5[OF copy_size])
  let ?ip = "sections_t_C.inst_pos_C sec"
  let ?ap = "sections_t_C.addr_pos_C sec"
  have inst_byte_room_nat: "unat ?ip < unat inst_cap"
    using inst_room by linarith
  have inst_byte_room: "?ip < inst_cap"
    using inst_byte_room_nat by (simp add: word_less_nat_alt)
  have inst_suc_unat: "unat (?ip + 1) = Suc (unat ?ip)"
    using inst_room unat_lt2p[of inst_cap] by unat_arith
  have inst_suc_room: "Suc (unat ?ip) \<le> unat inst_cap"
    using inst_room by linarith
  have inst_suc_dist: "ptr_range_distinct inst (Suc (unat ?ip))"
    by (rule ptr_range_distinct_mono[OF inst_dist inst_suc_room])
  have inst_byte_ptr:
    "ptr_valid (heap_typing s) (inst +\<^sub>p uint ?ip)"
    by (rule buf_valid_uintD[OF inst_valid inst_byte_room_nat])
  have inst_byte_disj1:
    "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    by (auto intro!: bufs_disjoint_int_uintD[
          OF out1_inst_disj _ inst_byte_room_nat])
  have inst_byte_disj2:
    "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    by (auto intro!: bufs_disjoint_int_uintD[
          OF out2_inst_disj _ inst_byte_room_nat])
  have inst_varint_room:
    "unat (?ip + 1) + unat sn \<le> unat inst_cap"
    using inst_room sn_le5 inst_suc_unat by linarith
  have inst_varint_no_overflow:
    "unat (?ip + 1) + unat sn < 2 ^ 32"
  proof -
    have "unat (?ip + 1) + unat sn \<le> unat inst_cap"
      by (rule inst_varint_room)
    also have "... < 2 ^ 32"
      using unat_lt2p[of inst_cap] by simp
    finally show ?thesis .
  qed
  have inst_varint_fits:
    "\<not> inst_cap - (?ip + 1) < sn"
    by (rule word_sub_not_less_of_unat_add_le[OF inst_varint_room])
  have inst_varint_valid:
    "\<forall>j < unat sn.
      ptr_valid (heap_typing s)
        (inst +\<^sub>p uint (?ip + 1 + of_nat j))"
    by (auto intro!: buf_valid_word_rangeD[
          OF inst_valid _ inst_varint_no_overflow inst_varint_room])
  have inst_varint_inj:
    "\<forall>i < unat sn. \<forall>j < unat sn.
      i \<noteq> j \<longrightarrow>
      inst +\<^sub>p uint (?ip + 1 + of_nat i) \<noteq>
      inst +\<^sub>p uint (?ip + 1 + of_nat j)"
    by (auto intro!: ptr_range_distinct_word_range_inj[
          OF inst_dist inst_varint_no_overflow inst_varint_room])
  have inst_varint_prefix_disj:
    "\<forall>k < unat (?ip + 1). \<forall>i.
      i < sn \<longrightarrow>
      inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < unat (?ip + 1)" and i_lt: "i < sn"
    show "inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
      by (rule ptr_range_distinct_word_prefix_disj[
        OF inst_dist inst_varint_no_overflow inst_varint_room k_lt i_lt])
  qed
  have inst_varint_disj1:
    "\<forall>k < out1_n. \<forall>i.
      i < sn \<longrightarrow>
      out1 +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < out1_n" and i_lt: "i < sn"
    show "out1 +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
        OF out1_inst_disj k_lt i_lt inst_varint_no_overflow
           inst_varint_room])
  qed
  have inst_varint_disj2:
    "\<forall>k < out2_n. \<forall>i.
      i < sn \<longrightarrow>
      out2 +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < out2_n" and i_lt: "i < sn"
    show "out2 +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
        OF out2_inst_disj k_lt i_lt inst_varint_no_overflow
           inst_varint_room])
  qed
  have addr_byte_room_nat: "unat ?ap < unat addr_cap"
    using addr_room by linarith
  have addr_byte_room: "?ap < addr_cap"
    using addr_byte_room_nat by (simp add: word_less_nat_alt)
  have addr_suc_room: "Suc (unat ?ap) \<le> unat addr_cap"
    using addr_room by linarith
  have addr_suc_dist: "ptr_range_distinct addr_buf (Suc (unat ?ap))"
    by (rule ptr_range_distinct_mono[OF addr_dist addr_suc_room])
  have addr_byte_ptr:
    "ptr_valid (heap_typing s) (addr_buf +\<^sub>p uint ?ap)"
    by (rule buf_valid_uintD[OF addr_valid addr_byte_room_nat])
  have addr_byte_disj1:
    "\<forall>i < out1_n. out1 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint ?ap"
    by (auto intro!: bufs_disjoint_int_uintD[
          OF out1_addr_disj _ addr_byte_room_nat])
  have addr_byte_disj2:
    "\<forall>i < out2_n. out2 +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint ?ap"
    by (auto intro!: bufs_disjoint_int_uintD[
          OF out2_addr_disj _ addr_byte_room_nat])
  have addr_varint_room:
    "unat ?ap + unat an \<le> unat addr_cap"
    using addr_room an_le5 by linarith
  have addr_varint_no_overflow:
    "unat ?ap + unat an < 2 ^ 32"
  proof -
    have "unat ?ap + unat an \<le> unat addr_cap"
      by (rule addr_varint_room)
    also have "... < 2 ^ 32"
      using unat_lt2p[of addr_cap] by simp
    finally show ?thesis .
  qed
  have addr_varint_fits:
    "\<not> addr_cap - ?ap < an"
    by (rule word_sub_not_less_of_unat_add_le[OF addr_varint_room])
  have addr_varint_valid:
    "\<forall>j < unat an.
      ptr_valid (heap_typing s)
        (addr_buf +\<^sub>p uint (?ap + of_nat j))"
    by (auto intro!: buf_valid_word_rangeD[
          OF addr_valid _ addr_varint_no_overflow addr_varint_room])
  have addr_varint_inj:
    "\<forall>i < unat an. \<forall>j < unat an.
      i \<noteq> j \<longrightarrow>
      addr_buf +\<^sub>p uint (?ap + of_nat i) \<noteq>
      addr_buf +\<^sub>p uint (?ap + of_nat j)"
    by (auto intro!: ptr_range_distinct_word_range_inj[
          OF addr_dist addr_varint_no_overflow addr_varint_room])
  have addr_varint_prefix_disj:
    "\<forall>k < unat ?ap. \<forall>i.
      i < an \<longrightarrow>
      addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (?ap + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < unat ?ap" and i_lt: "i < an"
    show "addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (?ap + i)"
      by (rule ptr_range_distinct_word_prefix_disj[
        OF addr_dist addr_varint_no_overflow addr_varint_room k_lt i_lt])
  qed
  have addr_varint_disj1:
    "\<forall>k < out1_n. \<forall>i.
      i < an \<longrightarrow>
      out1 +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (?ap + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < out1_n" and i_lt: "i < an"
    show "out1 +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (?ap + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
        OF out1_addr_disj k_lt i_lt addr_varint_no_overflow
           addr_varint_room])
  qed
  have addr_varint_disj2:
    "\<forall>k < out2_n. \<forall>i.
      i < an \<longrightarrow>
      out2 +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (?ap + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < out2_n" and i_lt: "i < an"
    show "out2 +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (?ap + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
        OF out2_addr_disj k_lt i_lt addr_varint_no_overflow
           addr_varint_room])
  qed
  show ?thesis
  proof (cases "(4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word)")
    case True
    have sz_ge: "(4 :: 32 word) \<le> copy_len"
      using True by simp
    have sz_le: "copy_len \<le> (18 :: 32 word)"
      using True by simp
    show ?thesis
    proof (cases "mode_t_C.mode_C m < (6 :: 32 word)")
      case True
      have frame:
        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
          \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec'.
              r = Result sec' \<and>
              sections_result sec'
                (sections_t_C.data_pos_C sec) (?ip + 1) (?ap + an)
                ENC_OK \<and>
              heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
              heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
              heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_small_addr_varint_success_heap_bytes2_frame[
          OF bm sz_ge sz_le True addr_size sec_ok near_ptr_lt
             inst_byte_room inst_byte_ptr inst_suc_dist inst_byte_disj1
             inst_byte_disj2 addr_varint_fits addr_varint_valid
             addr_varint_inj addr_varint_prefix_disj
             addr_varint_no_overflow addr_varint_disj1
             addr_varint_disj2])
      have cache:
        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
          \<bullet> s
         \<lbrace> \<lambda>r t.
             (\<exists>sec'.
               r = Result sec' \<and>
               enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
               enc_cache_wf (cache_update c (unat copy_addr))) \<and>
             heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_small_addr_varint_success_enc_cache_abs[
          OF abs wf bm sz_ge sz_le True addr_size inst_byte_room
             inst_byte_ptr addr_varint_fits addr_varint_valid])
	      have combined:
	        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
	          \<bullet> s
         \<lbrace> \<lambda>r t.
             ((\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec) (?ip + 1) (?ap + an)
                  ENC_OK \<and>
                heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                heap_typing t = heap_typing s) \<and>
              ((\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c (unat copy_addr))) \<and>
	                heap_typing t = heap_typing s)) \<rbrace>"
	        using frame cache by (simp add: runs_to_conj)
	      show ?thesis
	        apply (rule runs_to_weaken[OF combined])
	        apply (erule emit_copy'_pack_heap_bytes2_cache_frame[
	          where inst_inc = "1 :: 32 word" and addr_inc = an])
	           apply simp
	          apply simp
	         apply simp
	        apply (rule an_le5)
	       apply (simp add: True)
	        done
    next
      case False
      have frame:
        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
          \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec'.
              r = Result sec' \<and>
              sections_result sec'
                (sections_t_C.data_pos_C sec) (?ip + 1) (?ap + 1)
                ENC_OK \<and>
              heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
              heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
              heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_small_addr_byte_success_heap_bytes2_frame[
          OF bm sz_ge sz_le False sec_ok near_ptr_lt inst_byte_room
             inst_byte_ptr inst_suc_dist inst_byte_disj1 inst_byte_disj2
             addr_byte_room addr_byte_ptr addr_suc_dist addr_byte_disj1
             addr_byte_disj2])
      have cache:
        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
          \<bullet> s
         \<lbrace> \<lambda>r t.
             (\<exists>sec'.
               r = Result sec' \<and>
               enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
               enc_cache_wf (cache_update c (unat copy_addr))) \<and>
             heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_small_addr_byte_success_enc_cache_abs[
          OF abs wf bm sz_ge sz_le False inst_byte_room inst_byte_ptr
             addr_byte_room addr_byte_ptr])
	      have combined:
	        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
	          \<bullet> s
         \<lbrace> \<lambda>r t.
             ((\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec) (?ip + 1) (?ap + 1)
                  ENC_OK \<and>
                heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                heap_typing t = heap_typing s) \<and>
              ((\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c (unat copy_addr))) \<and>
	                heap_typing t = heap_typing s)) \<rbrace>"
	        using frame cache by (simp add: runs_to_conj)
	      show ?thesis
	        apply (rule runs_to_weaken[OF combined])
	        apply (erule emit_copy'_pack_heap_bytes2_cache_frame[
	          where inst_inc = "1 :: 32 word" and addr_inc = "1 :: 32 word"])
	           apply simp
	          apply simp
	         apply simp
	        apply simp
	       apply (simp add: False)
	        done
    qed
  next
    case False
    have sz_large:
      "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
      using False .
    have inst_inc_le: "unat ((1 :: 32 word) + sn) \<le> 6"
      using sn_le5 by (simp add: unat_word_ariths)
    show ?thesis
    proof (cases "mode_t_C.mode_C m < (6 :: 32 word)")
      case True
      have frame:
        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
          \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec'.
              r = Result sec' \<and>
              sections_result sec'
                (sections_t_C.data_pos_C sec) (?ip + 1 + sn) (?ap + an)
                ENC_OK \<and>
              heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
              heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
              heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_large_addr_varint_success_heap_bytes2_frame[
          OF bm sz_large copy_size True addr_size sec_ok near_ptr_lt
             inst_byte_room inst_byte_ptr inst_suc_dist inst_byte_disj1
             inst_byte_disj2 inst_varint_fits inst_varint_valid
             inst_varint_inj inst_varint_prefix_disj
             inst_varint_no_overflow inst_varint_disj1 inst_varint_disj2
             addr_varint_fits addr_varint_valid addr_varint_inj
             addr_varint_prefix_disj addr_varint_no_overflow
             addr_varint_disj1 addr_varint_disj2])
      have cache:
        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
          \<bullet> s
         \<lbrace> \<lambda>r t.
             (\<exists>sec'.
               r = Result sec' \<and>
               enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
               enc_cache_wf (cache_update c (unat copy_addr))) \<and>
             heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_large_addr_varint_success_enc_cache_abs[
          OF abs wf bm sz_large copy_size True addr_size inst_byte_room
             inst_byte_ptr inst_varint_fits inst_varint_valid
             addr_varint_fits addr_varint_valid])
	      have combined:
	        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
	          \<bullet> s
         \<lbrace> \<lambda>r t.
             ((\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec) (?ip + 1 + sn) (?ap + an)
                  ENC_OK \<and>
                heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                heap_typing t = heap_typing s) \<and>
              ((\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c (unat copy_addr))) \<and>
	                heap_typing t = heap_typing s)) \<rbrace>"
	        using frame cache by (simp add: runs_to_conj)
	      show ?thesis
	        apply (rule runs_to_weaken[OF combined])
	        apply (erule emit_copy'_pack_heap_bytes2_cache_frame[
	          where inst_inc = "(1 :: 32 word) + sn" and addr_inc = an])
	           apply (simp add: add.assoc)
	          apply simp
	         apply (rule inst_inc_le)
	        apply (rule an_le5)
	       apply (simp add: True)
	        done
    next
      case False
      have frame:
        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
          \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec'.
              r = Result sec' \<and>
              sections_result sec'
                (sections_t_C.data_pos_C sec) (?ip + 1 + sn) (?ap + 1)
                ENC_OK \<and>
              heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
              heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
              heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_large_addr_byte_success_heap_bytes2_frame[
          OF bm sz_large copy_size False sec_ok near_ptr_lt inst_byte_room
             inst_byte_ptr inst_suc_dist inst_byte_disj1 inst_byte_disj2
             inst_varint_fits inst_varint_valid inst_varint_inj
             inst_varint_prefix_disj inst_varint_no_overflow
             inst_varint_disj1 inst_varint_disj2 addr_byte_room
             addr_byte_ptr addr_suc_dist addr_byte_disj1 addr_byte_disj2])
      have cache:
        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
          \<bullet> s
         \<lbrace> \<lambda>r t.
             (\<exists>sec'.
               r = Result sec' \<and>
               enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
               enc_cache_wf (cache_update c (unat copy_addr))) \<and>
             heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_large_addr_byte_success_enc_cache_abs[
          OF abs wf bm sz_large copy_size False inst_byte_room
             inst_byte_ptr inst_varint_fits inst_varint_valid
             addr_byte_room addr_byte_ptr])
	      have combined:
	        "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
	          \<bullet> s
         \<lbrace> \<lambda>r t.
             ((\<exists>sec'.
                r = Result sec' \<and>
                sections_result sec'
                  (sections_t_C.data_pos_C sec) (?ip + 1 + sn) (?ap + 1)
                  ENC_OK \<and>
                heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                heap_typing t = heap_typing s) \<and>
              ((\<exists>sec'.
                r = Result sec' \<and>
                enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c (unat copy_addr))) \<and>
	                heap_typing t = heap_typing s)) \<rbrace>"
	        using frame cache by (simp add: runs_to_conj)
	      show ?thesis
	        apply (rule runs_to_weaken[OF combined])
	        apply (erule emit_copy'_pack_heap_bytes2_cache_frame[
	          where inst_inc = "(1 :: 32 word) + sn" and addr_inc = "1 :: 32 word"])
	           apply (simp add: add.assoc)
	          apply simp
	         apply (rule inst_inc_le)
	        apply simp
	       apply (simp add: False)
	        done
    qed
  qed
qed

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
           f \<leftarrow> liftE
                (try_emit_add_copy' sec data data_cap inst inst_cap
                  addr addr_cap pending pend_len
                  (match_t_C.pos_C m) (src_len + tp) (match_t_C.len_C m));
           unless (sections_t_C.err_C (fused_t_C.s_C f) = 0)
            (throw (fused_t_C.s_C f));
           condition (\<lambda>s. fused_t_C.fused_C f \<noteq> 0)
             (do {
                (sec, tp) \<leftarrow>
                  condition (\<lambda>s. fused_t_C.fused_C f < match_t_C.len_C m)
                    (do {
                       sec \<leftarrow> liftE
                         (emit_copy' (fused_t_C.s_C f) inst inst_cap
                           addr addr_cap
                           (match_t_C.pos_C m + fused_t_C.fused_C f)
                           (src_len + (tp + fused_t_C.fused_C f))
                           (match_t_C.len_C m - fused_t_C.fused_C f));
                       unless (sections_t_C.err_C sec = 0) (throw sec);
                       return (sec, tp + match_t_C.len_C m)
                     })
                    (return (fused_t_C.s_C f, tp + fused_t_C.fused_C f));
                return (0, sec, tp)
              })
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
              })
         })
    })"

definition encode_window_c_match_branch ::
  "32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   sections_t_C \<Rightarrow> 32 word \<Rightarrow> match_t_C \<Rightarrow>
   (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
    lifted_globals) exn_monad" where
  "encode_window_c_match_branch src_len
      data data_cap inst inst_cap addr addr_cap pending pend_len sec tp m =
    (do {
       f \<leftarrow> liftE
         (try_emit_add_copy' sec data data_cap inst inst_cap
           addr addr_cap pending pend_len
           (match_t_C.pos_C m) (src_len + tp) (match_t_C.len_C m));
       unless (sections_t_C.err_C (fused_t_C.s_C f) = 0)
         (throw (fused_t_C.s_C f));
       condition (\<lambda>s. fused_t_C.fused_C f \<noteq> 0)
         (do {
            (sec, tp) \<leftarrow>
              condition (\<lambda>s. fused_t_C.fused_C f < match_t_C.len_C m)
                (do {
                   sec \<leftarrow> liftE
                     (emit_copy' (fused_t_C.s_C f) inst inst_cap addr addr_cap
                       (match_t_C.pos_C m + fused_t_C.fused_C f)
                       (src_len + (tp + fused_t_C.fused_C f))
                       (match_t_C.len_C m - fused_t_C.fused_C f));
                   unless (sections_t_C.err_C sec = 0) (throw sec);
                   return (sec, tp + match_t_C.len_C m)
                 })
                (return (fused_t_C.s_C f, tp + fused_t_C.fused_C f));
            return (0, sec, tp)
          })
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
proof -
  have rel: "source_index_heap_rel s src_bytes head_arr next_arr"
    using index by (simp add: encoder_index_post_def)
  have nexts_wf: "source_index_heap_nexts_wf s src_bytes next_arr"
    using index by (simp add: encoder_index_post_def)
  have closed: "source_index_heap_chains_closed s src_bytes head_arr next_arr"
    using index by (simp add: encoder_index_post_def)
  have src_bytes_eq: "src_bytes = heap_bytes s src (unat src_len)"
    using index by (simp add: encoder_index_post_def)
  have tgt_bytes_eq: "tgt_bytes = heap_bytes s tgt (unat tgt_len)"
    using index by (simp add: encoder_index_post_def)
  have typing: "heap_typing s = heap_typing s0"
    using index by (simp add: encoder_index_post_def)
  have tgt_ok0: "buf_valid s0 tgt (unat tgt_len)"
    using buffers by (simp add: encoder_buffers_ok_def)
  have tgt_ok: "buf_valid s tgt (unat tgt_len)"
    using tgt_ok0 typing by (simp add: buf_valid_def)
  show ?thesis
    unfolding encode_window_match_rel_def
  proof (intro allI impI conjI)
    fix tp m
    assume tp_le: "tp \<le> tgt_len"
      and result:
        "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
          Some m"
    show "m = (let best =
              find_best_match_spec src_bytes tgt_bytes (unat tp)
                (build_index_spec src_bytes)
            in match_t_C (of_nat (em_pos best)) (of_nat (em_len best)))"
      unfolding Let_def
      by (rule find_best_match'_eq_find_best_match_spec_bytes[
          OF src_bytes_eq tgt_bytes_eq rel closed nexts_wf tp_le tgt_ok
             result])
    show "match_valid src_bytes tgt_bytes (unat tp)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
      by (rule find_best_match'_match_valid_heap_bytes_source_index_bytes[
          OF src_bytes_eq tgt_bytes_eq rel nexts_wf tp_le result])
  qed
qed

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
      and cache:
    "enc_cache_abs s (enc_cache enc_full_init)"
    "enc_cache_wf (enc_cache enc_full_init)"
  shows "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec 0 0 src_bytes tgt_bytes enc_full_init"
proof -
  have sections:
    "enc_sections_state_rel s data inst addr sec enc_full_init"
    by (rule enc_sections_state_rel_empty[OF sec_zero(1-3)])
  show ?thesis
    unfolding encode_window_loop_rel_def
    using bytes sec_zero sections cache buffers
    by (simp add: enc_full_init_def heap_bytes_word_def
        encode_window_loop_buffers_ok_def)
qed

lemma encode_window_initial_loop_budget_rel:
  assumes input:
    "encoder_input_rel s0 src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and final_caps:
    "encoder_final_section_caps_ok src_bytes tgt_bytes
      data_cap inst_cap addr_cap"
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
      and cache:
    "enc_cache_abs s (enc_cache enc_full_init)"
    "enc_cache_wf (enc_cache enc_full_init)"
  shows "encode_window_loop_budget_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec 0 0 src_bytes tgt_bytes enc_full_init"
proof -
  have sections:
    "enc_sections_state_rel s data inst addr sec enc_full_init"
    by (rule enc_sections_state_rel_empty[OF sec_zero(1-3)])
  have budget:
    "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap enc_full_init"
    unfolding encode_window_section_budget_def
      encode_window_spec_reaches_final_def
      encode_window_section_prefix_budget_def
      encode_window_final_spec_state_def
    using final_caps
    by (simp add: enc_full_init_def)
  show ?thesis
    unfolding encode_window_loop_budget_rel_def
    using bytes sec_zero sections cache buffers budget
    by (simp add: enc_full_init_def heap_bytes_word_def
        encode_window_loop_buffers_ok_def)
qed

lemma encode_window_pending_byte_step_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and pend_lt: "pend_len < pending_cap"
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
proof -
  let ?byte = "tgt_bytes ! unat tp"
  let ?written = "heap_w8 s (tgt +\<^sub>p uint tp)"
  let ?t =
    "heap_w8_update
      (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
             ?written)) s"
  let ?spec = "buffer_pending_byte_spec ?byte spec_st"
  have update_eq:
    "heap_w8_update
       (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
              h (tgt +\<^sub>p uint tp))) s = ?t"
    by simp
  have pend_nat_lt: "unat pend_len < unat pending_cap"
    using pend_lt by (simp add: word_less_nat_alt)
  have tp_nat_lt: "unat tp < unat tgt_len"
    using tp_lt by (simp add: word_less_nat_alt)
  have tp_suc_le: "Suc (unat tp) \<le> unat tgt_len"
    using tp_nat_lt by simp
  have pend_suc: "unat (pend_len + 1) = Suc (unat pend_len)"
    by (rule unat_suc_word_less[OF pend_lt])
  have tp_suc: "unat (tp + 1) = Suc (unat tp)"
    by (rule unat_suc_word_less[OF tp_lt])

  have pending_valid: "buf_valid s pending (unat pending_cap)"
    and tgt_valid: "buf_valid s tgt (unat tgt_len)"
    and pending_dist: "ptr_range_distinct pending (unat pending_cap)"
    and pending_src:
      "bufs_disjoint pending (unat pending_cap) src (unat src_len)"
    and pending_tgt:
      "bufs_disjoint pending (unat pending_cap) tgt (unat tgt_len)"
    and pending_data:
      "bufs_disjoint pending (unat pending_cap) data (unat data_cap)"
    and pending_inst:
      "bufs_disjoint pending (unat pending_cap) inst (unat inst_cap)"
    and pending_addr:
      "bufs_disjoint pending (unat pending_cap) addr (unat addr_cap)"
    using buffers
    by (simp_all add: encode_window_loop_buffers_ok_def)
  have pending_ptr:
    "ptr_valid (heap_typing s) (pending +\<^sub>p uint pend_len)"
    by (rule buf_valid_uintD[OF pending_valid pend_nat_lt])
  have tgt_ptr:
    "ptr_valid (heap_typing s) (tgt +\<^sub>p uint tp)"
    by (rule buf_valid_uintD[OF tgt_valid tp_nat_lt])

  have src_heap:
    "heap_bytes ?t src (unat src_len) = src_bytes"
  proof -
    have src_pending:
      "bufs_disjoint src (unat src_len) pending (unat pending_cap)"
      using pending_src by (simp add: bufs_disjoint_sym)
    have "heap_bytes ?t src (unat src_len) = heap_bytes s src (unat src_len)"
      by (rule heap_bytes_update_disjoint_prefix[
          OF src_pending pend_nat_lt order.refl])
    thus ?thesis
      using rel by (simp add: encode_window_loop_rel_def)
  qed
  have tgt_heap:
    "heap_bytes ?t tgt (unat tgt_len) = tgt_bytes"
  proof -
    have tgt_pending:
      "bufs_disjoint tgt (unat tgt_len) pending (unat pending_cap)"
      using pending_tgt by (simp add: bufs_disjoint_sym)
    have "heap_bytes ?t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)"
      by (rule heap_bytes_update_disjoint_prefix[
          OF tgt_pending pend_nat_lt order.refl])
    thus ?thesis
      using rel by (simp add: encode_window_loop_rel_def)
  qed
  have tgt_byte:
    "?written = ?byte"
  proof -
    have tgt_bytes_eq: "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
      using rel by (simp add: encode_window_loop_rel_def)
    have nth_heap:
      "heap_bytes s tgt (unat tgt_len) ! unat tp =
       heap_w8 s (tgt +\<^sub>p int (unat tp))"
      by (rule heap_bytes_nth[OF tp_nat_lt])
    have byte_eq:
      "tgt_bytes ! unat tp =
       heap_w8 s (tgt +\<^sub>p int (unat tp))"
      using tgt_bytes_eq nth_heap by simp
    show ?thesis
      using byte_eq[symmetric] by (simp only: uint_nat)
  qed
  have pending_heap:
    "heap_bytes_word ?t pending 0 (pend_len + 1) =
       enc_pending ?spec"
  proof -
    have append:
      "heap_bytes_word ?t pending 0 (pend_len + 1) =
       heap_bytes_word s pending 0 pend_len @
       [?written]"
      by (rule heap_bytes_word_zero_update_append[OF pend_lt pending_dist])
    show ?thesis
      using append rel tgt_byte
      by (simp add: encode_window_loop_rel_def buffer_pending_byte_spec_def)
  qed
  have data_heap:
    "heap_bytes ?t data (unat (sections_t_C.data_pos_C sec)) =
     heap_bytes s data (unat (sections_t_C.data_pos_C sec))"
  proof -
    have data_pending:
      "bufs_disjoint data (unat data_cap) pending (unat pending_cap)"
      using pending_data by (simp add: bufs_disjoint_sym)
    have data_le:
      "unat (sections_t_C.data_pos_C sec) \<le> unat data_cap"
      using rel by (simp add: encode_window_loop_rel_def)
    show ?thesis
      by (rule heap_bytes_update_disjoint_prefix[
          OF data_pending pend_nat_lt data_le])
  qed
  have inst_heap:
    "heap_bytes ?t inst (unat (sections_t_C.inst_pos_C sec)) =
     heap_bytes s inst (unat (sections_t_C.inst_pos_C sec))"
  proof -
    have inst_pending:
      "bufs_disjoint inst (unat inst_cap) pending (unat pending_cap)"
      using pending_inst by (simp add: bufs_disjoint_sym)
    have inst_le:
      "unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap"
      using rel by (simp add: encode_window_loop_rel_def)
    show ?thesis
      by (rule heap_bytes_update_disjoint_prefix[
          OF inst_pending pend_nat_lt inst_le])
  qed
  have addr_heap:
    "heap_bytes ?t addr (unat (sections_t_C.addr_pos_C sec)) =
     heap_bytes s addr (unat (sections_t_C.addr_pos_C sec))"
  proof -
    have addr_pending:
      "bufs_disjoint addr (unat addr_cap) pending (unat pending_cap)"
      using pending_addr by (simp add: bufs_disjoint_sym)
    have addr_le:
      "unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"
      using rel by (simp add: encode_window_loop_rel_def)
    show ?thesis
      by (rule heap_bytes_update_disjoint_prefix[
          OF addr_pending pend_nat_lt addr_le])
  qed
  have sections_rel:
    "enc_sections_state_rel ?t data inst addr sec ?spec"
    using rel data_heap inst_heap addr_heap
    by (simp add: encode_window_loop_rel_def enc_sections_state_rel_def
                  emitted_sections_def buffer_pending_byte_spec_def)
  have slack_step:
    "Suc (unat pend_len) + (unat tgt_len - Suc (unat tp)) =
     unat pend_len + (unat tgt_len - unat tp)"
    using tp_nat_lt by simp
  have data_slack:
    "unat (sections_t_C.data_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat data_cap"
    using rel unfolding encode_window_loop_rel_def by blast
  have inst_slack:
    "unat (sections_t_C.inst_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat inst_cap"
    using rel unfolding encode_window_loop_rel_def by blast
  have addr_slack:
    "unat (sections_t_C.addr_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat addr_cap"
    using rel unfolding encode_window_loop_rel_def by blast
  have data_slack_after:
    "unat (sections_t_C.data_pos_C sec) + Suc (unat pend_len) +
       (unat tgt_len - Suc (unat tp)) + 64 \<le> unat data_cap"
    using data_slack slack_step by linarith
  have inst_slack_after:
    "unat (sections_t_C.inst_pos_C sec) + Suc (unat pend_len) +
       (unat tgt_len - Suc (unat tp)) + 64 \<le> unat inst_cap"
    using inst_slack slack_step by linarith
  have addr_slack_after:
    "unat (sections_t_C.addr_pos_C sec) + Suc (unat pend_len) +
       (unat tgt_len - Suc (unat tp)) + 64 \<le> unat addr_cap"
    using addr_slack slack_step by linarith
  have rel_after:
    "encode_window_loop_rel ?t src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec (tp + 1) (pend_len + 1) src_bytes tgt_bytes ?spec"
    using rel src_heap tgt_heap pending_heap sections_rel
      pend_suc tp_suc pend_nat_lt data_slack_after inst_slack_after
      addr_slack_after tp_suc_le
    by (auto simp: encode_window_loop_rel_def
                   buffer_pending_byte_spec_def word_less_nat_alt)
  have measure_after:
    "(((pend_len + 1, sec, tp + 1), ?t), ((pend_len, sec, tp), s)) \<in>
      measure
        (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
           unat tgt_len - unat tp)"
    using tp_nat_lt tp_suc by simp
  have find_run:
    "gets_the (find_best_match' src src_len tgt tgt_len tp head_arr next_arr)
      \<bullet> s \<lbrace> \<lambda>r t. t = s \<and> r = Result m \<rbrace>"
    unfolding gets_the_def
    apply runs_to_vcg
    using match by simp
  have short_branch: "match_t_C.len_C m < (4 :: 32 word)"
    using short by (simp add: min_match_def)
  have cap_branch: "\<not> pending_cap \<le> pend_len"
    using pend_lt by simp
  show ?thesis
    unfolding encode_window_c_loop_body_def
    apply simp
    apply (rule runs_to_bind)
     apply (rule runs_to_weaken[OF find_run])
    apply clarsimp
    using short_branch cap_branch
    apply simp
    apply runs_to_vcg
    using pending_ptr tgt_ptr rel_after measure_after update_eq
    apply (auto simp: update_eq)
    done
qed

lemma encode_window_try_fused_copy_step_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and tp_lt: "tp < tgt_len"
      and match:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
      and match_len: "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
      and fused:
    "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st =
      Some spec_st'"
  shows "encode_window_c_match_branch src_len
            data data_cap inst inst_cap addr addr_cap pending pend_len
            sec tp m \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st''.
              r = Result (pend_len', sec', tp') \<and>
              encode_window_loop_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st'' \<and>
              enc_tp spec_st < enc_tp spec_st'' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp) \<rbrace>"
proof -
  have copy_ge: "(4 :: 32 word) \<le> match_t_C.len_C m"
    using match_len by (simp add: min_match_def)
  have pending_len:
    "length (enc_pending spec_st) = unat pend_len"
    using rel by (simp add: encode_window_loop_rel_def)
  have pend_ge_nat: "1 \<le> unat pend_len"
    and pend_le_nat: "unat pend_len \<le> 4"
    using fused pending_len
    by (auto simp: try_emit_add_copy_spec_def Let_def min_match_def
             split: option.splits prod.splits if_splits)
  have pend_ge: "(1 :: 32 word) \<le> pend_len"
    using pend_ge_nat by (simp add: word_le_nat_alt)
  have pend_le: "pend_len \<le> (4 :: 32 word)"
    using pend_le_nat by (simp add: word_le_nat_alt)
  have abs: "enc_cache_abs s (enc_cache spec_st)"
    and cache_wf: "enc_cache_wf (enc_cache spec_st)"
    using rel by (simp_all add: encode_window_loop_rel_def)
  obtain bm where bm:
    "best_mode' (match_t_C.pos_C m) (src_len + tp) s = Some bm"
    by (rule best_mode'_some[OF abs cache_wf])
  have mode_wf:
    "enc_mode_arg_wf (enc_cache spec_st) (match_t_C.pos_C m)
      (src_len + tp) bm"
    by (rule best_mode'_encode_address_correct[OF abs cache_wf bm])
  have mode_le8: "mode_t_C.mode_C bm \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  obtain an where addr_size:
    "varint_size' (mode_t_C.arg_C bm) s = Some an"
    using varint_size'_some by blast
  have addr_size_any:
    "\<And>st. varint_size' (mode_t_C.arg_C bm) st = Some an"
    using addr_size varint_size'_state_independent[
      of "mode_t_C.arg_C bm" _ s]
    by simp
  have addr_exact:
    "encode_address (enc_cache spec_st) (unat (match_t_C.pos_C m))
       (unat (src_len + tp)) =
     (unat (mode_t_C.mode_C bm),
      enc_best_bytes (mode_t_C.mode_C bm) (mode_t_C.arg_C bm),
      cache_update (enc_cache spec_st) (unat (match_t_C.pos_C m)))"
    by (rule best_mode'_encode_address_exact[OF abs cache_wf bm])
  have addr_exact_le5:
    "mode_t_C.mode_C bm \<le> (5 :: 32 word) \<Longrightarrow>
     encode_address (enc_cache spec_st) (unat (match_t_C.pos_C m))
       (unat (src_len + tp)) =
     (unat (mode_t_C.mode_C bm),
      varint_bytes32 (mode_t_C.arg_C bm) an,
      cache_update (enc_cache spec_st) (unat (match_t_C.pos_C m)))"
    using addr_exact addr_size varint_bytes32_eq_varint_encode[OF addr_size]
    by (simp add: enc_best_bytes_def word_le_nat_alt word_less_nat_alt)
  have addr_exact_gt5:
    "(5 :: 32 word) < mode_t_C.mode_C bm \<Longrightarrow>
     encode_address (enc_cache spec_st) (unat (match_t_C.pos_C m))
       (unat (src_len + tp)) =
     (unat (mode_t_C.mode_C bm),
      [ucast (mode_t_C.arg_C bm)],
      cache_update (enc_cache spec_st) (unat (match_t_C.pos_C m)))"
    using addr_exact
    by (simp add: enc_best_bytes_def word_less_nat_alt)
  have spec_mode_gt5_copy_ne4_none:
    "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st = None"
    if mode_gt: "(5 :: 32 word) < mode_t_C.mode_C bm"
      and copy_ne: "match_t_C.len_C m \<noteq> (4 :: 32 word)"
  proof -
    have src_tp_no_overflow: "unat src_len + unat tp < 2 ^ 32"
      using rel src_tgt_bound tp_lt
      by (auto simp: encode_window_loop_rel_def word_less_nat_alt)
    have here_eq:
      "length src_bytes + enc_tp spec_st = unat (src_len + tp)"
      using rel src_tp_no_overflow
      by (simp add: encode_window_loop_rel_def unat_word_ariths
                    word_less_nat_alt)
    have addr_choice:
      "encode_address (enc_cache spec_st) (unat (match_t_C.pos_C m))
         (length src_bytes + enc_tp spec_st) =
       (unat (mode_t_C.mode_C bm), [ucast (mode_t_C.arg_C bm)],
        cache_update (enc_cache spec_st) (unat (match_t_C.pos_C m)))"
      using addr_exact_gt5[OF mode_gt] here_eq by simp
    show ?thesis
      by (rule try_emit_add_copy_spec_mode_gt5_copy_ne4_none[
          OF addr_choice mode_gt copy_ne])
  qed
  have spec_mode_gt5_copy_ne4_false:
    False
    if mode_gt: "(5 :: 32 word) < mode_t_C.mode_C bm"
      and copy_ne: "match_t_C.len_C m \<noteq> (4 :: 32 word)"
    using fused spec_mode_gt5_copy_ne4_none[OF mode_gt copy_ne] by simp
	  have op_nz_le5_gt6:
	    "mode_t_C.mode_C bm \<le> (5 :: 32 word) \<Longrightarrow>
	     (0xA2 + (mode_t_C.mode_C bm * 0xC + pend_len * 3) :: 32 word) \<noteq> 0"
  proof -
    assume mode_le: "mode_t_C.mode_C bm \<le> (5 :: 32 word)"
    have mode_nat: "unat (mode_t_C.mode_C bm) \<le> 5"
      using mode_le by (simp add: word_le_nat_alt)
    have pend_nat: "1 \<le> unat pend_len" "unat pend_len \<le> 4"
      using pend_ge pend_le by (simp_all add: word_le_nat_alt)
    have expr_unat:
      "unat (0xA2 + (mode_t_C.mode_C bm * 0xC + pend_len * 3) :: 32 word) =
       162 + (unat (mode_t_C.mode_C bm) * 12 + unat pend_len * 3)"
      using mode_nat pend_nat
      by (simp add: unat_word_ariths)
	    show ?thesis
	      using expr_unat pend_nat by auto
	  qed
	  have op_nz_le5_le6:
	    "mode_t_C.mode_C bm \<le> (5 :: 32 word) \<Longrightarrow>
	     match_t_C.len_C m \<le> (6 :: 32 word) \<Longrightarrow>
	     (0x9C + (mode_t_C.mode_C bm * 0xC +
	        (pend_len * 3 + match_t_C.len_C m)) :: 32 word) \<noteq> 0"
	    using pend_ge pend_le copy_ge
	    by (intro add_copy_opcode_word_mode_le5_le6_expr_nonzero)
		  have op_a0_nz:
		    "(0xA0 + (mode_t_C.mode_C bm * 0xC + pend_len * 3) :: 32 word) \<noteq> 0"
		  proof -
		    have mode_nat: "unat (mode_t_C.mode_C bm) \<le> 8"
	      using mode_le8 by (simp add: word_le_nat_alt)
	    have pend_nat: "1 \<le> unat pend_len" "unat pend_len \<le> 4"
	      using pend_ge pend_le by (simp_all add: word_le_nat_alt)
	    have expr_unat:
	      "unat (0xA0 + (mode_t_C.mode_C bm * 0xC + pend_len * 3) :: 32 word) =
	       160 + (unat (mode_t_C.mode_C bm) * 12 + unat pend_len * 3)"
	      using mode_nat pend_nat
	      by (simp add: unat_word_ariths)
		    show ?thesis
		      using expr_unat pend_nat by auto
		  qed
			  have op_d2_nz_gt5:
			    "\<not> mode_t_C.mode_C bm \<le> (5 :: 32 word) \<Longrightarrow>
			     (0xD2 + (mode_t_C.mode_C bm * 4 + pend_len) :: 32 word) \<noteq> 0"
		  proof -
		    assume mode_not_le: "\<not> mode_t_C.mode_C bm \<le> (5 :: 32 word)"
		    have mode_gt_nat: "5 < unat (mode_t_C.mode_C bm)"
		      using mode_not_le by (simp add: word_le_nat_alt)
		    have mode_le_nat: "unat (mode_t_C.mode_C bm) \<le> 8"
		      using mode_le8 by (simp add: word_le_nat_alt)
		    have pend_nat: "1 \<le> unat pend_len" "unat pend_len \<le> 4"
		      using pend_ge pend_le by (simp_all add: word_le_nat_alt)
		    have expr_unat:
		      "unat (0xD2 + (mode_t_C.mode_C bm * 4 + pend_len) :: 32 word) =
		       210 + (unat (mode_t_C.mode_C bm) * 4 + unat pend_len)"
		      using mode_le_nat pend_nat
		      by (simp add: unat_word_ariths)
			    show ?thesis
			      using expr_unat mode_gt_nat pend_nat by auto
			  qed
				  have op_d2_nz_gt5_nat:
				    "\<not> unat (mode_t_C.mode_C bm) \<le> 5 \<Longrightarrow>
				     (0xD2 + (mode_t_C.mode_C bm * 4 + pend_len) :: 32 word) \<noteq> 0"
				    using op_d2_nz_gt5 by (simp add: word_le_nat_alt)
			  have op_gt5_nz_nat:
			    "\<not> unat (mode_t_C.mode_C bm) \<le> 5 \<Longrightarrow>
			     (235 + (mode_t_C.mode_C bm - 6) * 4 + (pend_len - 1) ::
			        32 word) \<noteq> 0"
			    using mode_le8 pend_ge pend_le
			    by (auto simp: word_le_nat_alt word_less_nat_alt
			                   word_neq_0_conv unat_word_ariths)
			  have mode_gt5_not_lt6_nat:
			    "\<not> unat (mode_t_C.mode_C bm) \<le> 5 \<Longrightarrow>
			      \<not> mode_t_C.mode_C bm < (6 :: 32 word)"
			    by (simp add: word_less_nat_alt)
				  have mode_gt5_of_not_nat_le5:
				    "\<not> unat (mode_t_C.mode_C bm) \<le> 5 \<Longrightarrow>
				      (5 :: 32 word) < mode_t_C.mode_C bm"
		    by (simp add: word_less_nat_alt)
		  have mode_nat_le5_not_word_le_contra:
		    "\<And>P. \<lbrakk>unat (mode_t_C.mode_C bm) \<le> 5;
		      \<not> mode_t_C.mode_C bm \<le> (5 :: 32 word)\<rbrakk> \<Longrightarrow> P"
		    by (simp add: word_le_nat_alt)
		  have mode_not_nat_le5_word_le_contra:
		    "\<And>P. \<lbrakk>\<not> unat (mode_t_C.mode_C bm) \<le> 5;
		      mode_t_C.mode_C bm \<le> (5 :: 32 word)\<rbrakk> \<Longrightarrow> P"
		    by (simp add: word_le_nat_alt)
		  have spec_mode_gt5_copy_ne4_false_nat:
		    "\<lbrakk>\<not> unat (mode_t_C.mode_C bm) \<le> 5;
		      match_t_C.len_C m \<noteq> (4 :: 32 word)\<rbrakk> \<Longrightarrow> False"
		    using spec_mode_gt5_copy_ne4_false
	      mode_gt5_of_not_nat_le5 by blast
  have src_heap0: "heap_bytes s src (unat src_len) = src_bytes"
    and tgt_heap0: "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
    and src_len_eq: "length src_bytes = unat src_len"
    and tgt_len_eq: "length tgt_bytes = unat tgt_len"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and tp_le_nat: "unat tp \<le> unat tgt_len"
    and pend_cap: "unat pend_len \<le> unat pending_cap"
    and data_pos_le: "unat (sections_t_C.data_pos_C sec) \<le> unat data_cap"
    and inst_pos_le: "unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap"
    and addr_pos_le: "unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"
    and data_slack:
      "unat (sections_t_C.data_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat data_cap"
    and inst_slack:
      "unat (sections_t_C.inst_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat inst_cap"
    and addr_slack:
      "unat (sections_t_C.addr_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat addr_cap"
    using rel by (auto simp: encode_window_loop_rel_def)
  have src_valid: "buf_valid s src (unat src_len)"
    and tgt_valid: "buf_valid s tgt (unat tgt_len)"
    and pending_valid: "buf_valid s pending (unat pending_cap)"
    and data_valid: "buf_valid s data (unat data_cap)"
    and inst_valid: "buf_valid s inst (unat inst_cap)"
    and addr_valid: "buf_valid s addr (unat addr_cap)"
	    and pending_dist: "ptr_range_distinct pending (unat pending_cap)"
	    and data_dist: "ptr_range_distinct data (unat data_cap)"
	    and inst_dist: "ptr_range_distinct inst (unat inst_cap)"
	    and addr_dist: "ptr_range_distinct addr (unat addr_cap)"
	    and pending_src: "bufs_disjoint pending (unat pending_cap) src (unat src_len)"
	    and pending_tgt: "bufs_disjoint pending (unat pending_cap) tgt (unat tgt_len)"
	    and pending_data: "bufs_disjoint pending (unat pending_cap) data (unat data_cap)"
	    and pending_inst: "bufs_disjoint pending (unat pending_cap) inst (unat inst_cap)"
	    and pending_addr: "bufs_disjoint pending (unat pending_cap) addr (unat addr_cap)"
	    and data_src: "bufs_disjoint data (unat data_cap) src (unat src_len)"
	    and data_tgt: "bufs_disjoint data (unat data_cap) tgt (unat tgt_len)"
	    and data_inst: "bufs_disjoint data (unat data_cap) inst (unat inst_cap)"
	    and data_addr: "bufs_disjoint data (unat data_cap) addr (unat addr_cap)"
	    and inst_src: "bufs_disjoint inst (unat inst_cap) src (unat src_len)"
	    and inst_tgt: "bufs_disjoint inst (unat inst_cap) tgt (unat tgt_len)"
	    and inst_addr: "bufs_disjoint inst (unat inst_cap) addr (unat addr_cap)"
	    and addr_src: "bufs_disjoint addr (unat addr_cap) src (unat src_len)"
	    and addr_tgt: "bufs_disjoint addr (unat addr_cap) tgt (unat tgt_len)"
	    using buffers by (auto simp: encode_window_loop_buffers_ok_def)
  have an_le5: "unat an \<le> 5"
    by (rule varint_size'_le5[OF addr_size])
  have inst_byte_room_nat:
    "unat (sections_t_C.inst_pos_C sec) < unat inst_cap"
    using inst_slack pend_ge_nat by linarith
  have inst_byte_room: "sections_t_C.inst_pos_C sec < inst_cap"
    using inst_byte_room_nat by (simp add: word_less_nat_alt)
  have data_pend_room:
    "unat (sections_t_C.data_pos_C sec) + unat pend_len \<le> unat data_cap"
    using data_slack by linarith
  have data_pend_no_overflow:
    "unat (sections_t_C.data_pos_C sec) + unat pend_len < 2 ^ 32"
  proof -
    have "unat (sections_t_C.data_pos_C sec) + unat pend_len \<le> unat data_cap"
      by (rule data_pend_room)
    also have "... < 2 ^ 32"
      using unat_lt2p[of data_cap] by simp
    finally show ?thesis .
  qed
  have addr_an_room:
    "unat (sections_t_C.addr_pos_C sec) + unat an \<le> unat addr_cap"
    using addr_slack an_le5 by linarith
  have addr_an_no_overflow:
    "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
  proof -
    have "unat (sections_t_C.addr_pos_C sec) + unat an \<le> unat addr_cap"
      by (rule addr_an_room)
    also have "... < 2 ^ 32"
      using unat_lt2p[of addr_cap] by simp
    finally show ?thesis .
  qed
  have inst_suc_room:
    "Suc (unat (sections_t_C.inst_pos_C sec)) \<le> unat inst_cap"
    using inst_byte_room_nat by simp
	  have inst_suc_dist:
	    "ptr_range_distinct inst (Suc (unat (sections_t_C.inst_pos_C sec)))"
	    by (rule ptr_range_distinct_mono[OF inst_dist inst_suc_room])
	  have inst_suc_unat:
	    "unat (sections_t_C.inst_pos_C sec + 1) =
	     Suc (unat (sections_t_C.inst_pos_C sec))"
	    using inst_suc_room unat_lt2p[of inst_cap] by unat_arith
	  have inst_byte_ptr:
	    "ptr_valid (heap_typing s)
	      (inst +\<^sub>p uint (sections_t_C.inst_pos_C sec))"
	    by (rule buf_valid_uintD[OF inst_valid inst_byte_room_nat])
	  have data_fits:
	    "\<not> data_cap - sections_t_C.data_pos_C sec < pend_len"
	    by (rule word_sub_not_less_of_unat_add_le[OF data_pend_room])
	  have data_fits_nat:
	    "\<not> unat (data_cap - sections_t_C.data_pos_C sec) < unat pend_len"
	  proof -
	    have "unat (data_cap - sections_t_C.data_pos_C sec) =
	        unat data_cap - unat (sections_t_C.data_pos_C sec)"
	      using data_pos_le by (simp add: unat_sub word_le_nat_alt)
	    then show ?thesis
	      using data_pend_room by linarith
	  qed
	  have addr_fits:
	    "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
	    by (rule word_sub_not_less_of_unat_add_le[OF addr_an_room])
	  have addr_fits_nat:
	    "\<not> unat (addr_cap - sections_t_C.addr_pos_C sec) < unat an"
	  proof -
	    have "unat (addr_cap - sections_t_C.addr_pos_C sec) =
	        unat addr_cap - unat (sections_t_C.addr_pos_C sec)"
	      using addr_pos_le by (simp add: unat_sub word_le_nat_alt)
	    then show ?thesis
	      using addr_an_room by linarith
	  qed
	  have data_write_valid:
	    "\<forall>j < unat pend_len.
	      ptr_valid (heap_typing s)
	        (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
	    by (auto intro!: buf_valid_word_rangeD[OF data_valid _ data_pend_no_overflow
	          data_pend_room])
	  have data_pend_unat:
	    "unat (sections_t_C.data_pos_C sec + pend_len) =
	     unat (sections_t_C.data_pos_C sec) + unat pend_len"
	    by (rule unat_word_add_no_overflow[OF data_pend_no_overflow])
	  have pending_write_valid:
	    "\<forall>j < unat pend_len.
	      ptr_valid (heap_typing s) (pending +\<^sub>p uint (of_nat j :: 32 word))"
  proof (intro allI impI)
    fix j
    assume j_lt: "j < unat pend_len"
    have j_cap: "j < unat pending_cap"
      using j_lt pend_cap by linarith
    have j_32: "j < 2 ^ 32"
      using j_cap unat_lt2p[of pending_cap] by simp
    have unat_j: "unat (of_nat j :: 32 word) = j"
      using j_32 by (simp add: unat_of_nat)
    show "ptr_valid (heap_typing s)
      (pending +\<^sub>p uint (of_nat j :: 32 word))"
      by (rule buf_valid_uintD[OF pending_valid])
        (simp add: unat_j j_cap)
  qed
	  have addr_write_valid:
	    "\<forall>j < unat an.
	      ptr_valid (heap_typing s)
	        (addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
	    by (auto intro!: buf_valid_word_rangeD[OF addr_valid _ addr_an_no_overflow
	          addr_an_room])
	  have addr_byte_room_nat:
	    "unat (sections_t_C.addr_pos_C sec) < unat addr_cap"
	    using addr_slack pend_ge_nat by linarith
	  have addr_byte_room: "sections_t_C.addr_pos_C sec < addr_cap"
	    using addr_byte_room_nat by (simp add: word_less_nat_alt)
	  have addr_suc_room:
	    "Suc (unat (sections_t_C.addr_pos_C sec)) \<le> unat addr_cap"
	    using addr_byte_room_nat by simp
	  have addr_suc_dist:
	    "ptr_range_distinct addr (Suc (unat (sections_t_C.addr_pos_C sec)))"
	    by (rule ptr_range_distinct_mono[OF addr_dist addr_suc_room])
	  have addr_byte_ptr:
	    "ptr_valid (heap_typing s)
	      (addr +\<^sub>p uint (sections_t_C.addr_pos_C sec))"
	    by (rule buf_valid_uintD[OF addr_valid addr_byte_room_nat])
		  have addr_write_inj:
		    "\<forall>i < unat an. \<forall>j < unat an.
		      i \<noteq> j \<longrightarrow>
		      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
		      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
	    by (auto intro!: ptr_range_distinct_word_range_inj[
	          OF addr_dist addr_an_no_overflow addr_an_room])
	  have addr_write_inj_nat:
	    "\<And>i j. \<lbrakk>i < unat an; j < unat an; i \<noteq> j\<rbrakk> \<Longrightarrow>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
	    using addr_write_inj by blast
	  have addr_prefix_disj:
	    "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
	      i < an \<longrightarrow>
	      addr +\<^sub>p int k \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  proof (intro allI impI)
    fix k i
    assume k_lt: "k < unat (sections_t_C.addr_pos_C sec)"
      and i_lt: "i < an"
    show "addr +\<^sub>p int k \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	      by (rule ptr_range_distinct_word_prefix_disj[
	          OF addr_dist addr_an_no_overflow addr_an_room k_lt i_lt])
	  qed
	  have addr_prefix_disj_word:
	    "\<And>k i. \<lbrakk>k < unat (sections_t_C.addr_pos_C sec); i < an\<rbrakk> \<Longrightarrow>
	      addr +\<^sub>p int k \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	    using addr_prefix_disj by blast
	  have src_inst_disj: "bufs_disjoint src (unat src_len) inst (unat inst_cap)"
	    using inst_src by (simp add: bufs_disjoint_sym)
  have tgt_inst_disj: "bufs_disjoint tgt (unat tgt_len) inst (unat inst_cap)"
    using inst_tgt by (simp add: bufs_disjoint_sym)
  have src_data_disj: "bufs_disjoint src (unat src_len) data (unat data_cap)"
    using data_src by (simp add: bufs_disjoint_sym)
  have tgt_data_disj: "bufs_disjoint tgt (unat tgt_len) data (unat data_cap)"
    using data_tgt by (simp add: bufs_disjoint_sym)
  have src_addr_disj: "bufs_disjoint src (unat src_len) addr (unat addr_cap)"
    using addr_src by (simp add: bufs_disjoint_sym)
	  have tgt_addr_disj: "bufs_disjoint tgt (unat tgt_len) addr (unat addr_cap)"
	    using addr_tgt by (simp add: bufs_disjoint_sym)
	  have data_pending_disj_buf:
	    "bufs_disjoint data (unat data_cap) pending (unat pending_cap)"
	    using pending_data by (simp add: bufs_disjoint_sym)
	  have inst_data_disj: "bufs_disjoint inst (unat inst_cap) data (unat data_cap)"
	    using data_inst by (simp add: bufs_disjoint_sym)
	  have addr_data_disj: "bufs_disjoint addr (unat addr_cap) data (unat data_cap)"
	    using data_addr by (simp add: bufs_disjoint_sym)
	  have addr_inst_disj: "bufs_disjoint addr (unat addr_cap) inst (unat inst_cap)"
	    using inst_addr by (simp add: bufs_disjoint_sym)
	  have inst_byte_data_disj:
	    "\<forall>i < unat (sections_t_C.data_pos_C sec).
	       data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
	  proof (intro allI impI)
	    fix i
	    assume i_lt: "i < unat (sections_t_C.data_pos_C sec)"
	    have i_cap: "i < unat data_cap"
	      using i_lt data_pos_le by linarith
	    show "data +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
	      by (rule bufs_disjoint_int_uintD[OF data_inst i_cap inst_byte_room_nat])
	  qed
	  have inst_byte_addr_disj:
	    "\<forall>i < unat (sections_t_C.addr_pos_C sec).
	       addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
	  proof (intro allI impI)
	    fix i
	    assume i_lt: "i < unat (sections_t_C.addr_pos_C sec)"
	    have i_cap: "i < unat addr_cap"
	      using i_lt addr_pos_le by linarith
	    show "addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
	      by (rule bufs_disjoint_int_uintD[
	        OF addr_inst_disj i_cap inst_byte_room_nat])
	  qed
	  have inst_byte_pending_disj:
	    "\<forall>i < unat pend_len.
	       pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq>
	       inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
	  proof (intro allI impI)
	    fix i
	    assume i_lt: "i < unat pend_len"
	    have i_cap: "i < unat pending_cap"
	      using i_lt pend_cap by linarith
	    have i_32: "i < 2 ^ 32"
	      using i_cap unat_lt2p[of pending_cap] by simp
	    have i_unat: "unat (of_nat i :: 32 word) = i"
	      using i_32 by (simp add: unat_of_nat)
	    show "pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq>
	      inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
	      by (rule bufs_disjoint_uint_uintD[OF pending_inst])
	        (simp_all add: i_unat i_cap inst_byte_room_nat)
	  qed
	  have data_pending_disj:
	    "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
	      pending +\<^sub>p uint (of_nat j :: 32 word)"
	  proof (intro allI impI)
	    fix i j
	    assume i_lt: "i < unat pend_len" and j_lt: "j < unat pend_len"
	    have data_i:
	      "unat (sections_t_C.data_pos_C sec + of_nat i :: 32 word) <
	       unat data_cap"
	      using i_lt data_pend_no_overflow data_pend_room
	      by (simp add: unat_add_of_nat_index)
	    have j_cap: "j < unat pending_cap"
	      using j_lt pend_cap by linarith
	    have j_32: "j < 2 ^ 32"
	      using j_cap unat_lt2p[of pending_cap] by simp
	    have j_unat: "unat (of_nat j :: 32 word) = j"
	      using j_32 by (simp add: unat_of_nat)
	    show "data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
	      pending +\<^sub>p uint (of_nat j :: 32 word)"
	      by (rule bufs_disjoint_uint_uintD[OF data_pending_disj_buf])
	        (simp_all add: data_i j_unat j_cap)
	  qed
	  have data_inj:
	    "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
	      i \<noteq> j \<longrightarrow>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat i) \<noteq>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j)"
	    by (auto intro!: ptr_range_distinct_word_range_inj[
	          OF data_dist data_pend_no_overflow data_pend_room])
	  have data_prefix_disj:
	    "\<forall>k < unat (sections_t_C.data_pos_C sec). \<forall>i.
	      i < pend_len \<longrightarrow>
	      data +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat (sections_t_C.data_pos_C sec)"
	      and i_lt: "i < pend_len"
	    show "data +\<^sub>p int k \<noteq>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	      by (rule ptr_range_distinct_word_prefix_disj[
	        OF data_dist data_pend_no_overflow data_pend_room k_lt i_lt])
	  qed
	  have data_inst_disj:
	    "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
	      i < pend_len \<longrightarrow>
	      inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat (sections_t_C.inst_pos_C sec + 1)"
	      and i_lt: "i < pend_len"
	    have k_cap: "k < unat inst_cap"
	      using k_lt inst_suc_unat inst_suc_room by linarith
	    show "inst +\<^sub>p int k \<noteq>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	      by (rule bufs_disjoint_word_range_rightD_word[
	        OF inst_data_disj k_cap i_lt data_pend_no_overflow data_pend_room])
	  qed
	  have data_addr_disj:
	    "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
	      i < pend_len \<longrightarrow>
	      addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat (sections_t_C.addr_pos_C sec)"
	      and i_lt: "i < pend_len"
	    have k_cap: "k < unat addr_cap"
	      using k_lt addr_pos_le by linarith
	    show "addr +\<^sub>p int k \<noteq>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	      by (rule bufs_disjoint_word_range_rightD_word[
	        OF addr_data_disj k_cap i_lt data_pend_no_overflow data_pend_room])
	  qed
	  have addr_byte_data_disj:
	    "\<forall>i < unat (sections_t_C.data_pos_C sec + pend_len).
	       data +\<^sub>p int i \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
	  proof (intro allI impI)
	    fix i
	    assume i_lt: "i < unat (sections_t_C.data_pos_C sec + pend_len)"
	    have i_cap: "i < unat data_cap"
	      using i_lt data_pend_unat data_pend_room by linarith
	    show "data +\<^sub>p int i \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
	      by (rule bufs_disjoint_int_uintD[OF data_addr i_cap addr_byte_room_nat])
	  qed
	  have addr_byte_inst_disj:
	    "\<forall>i < unat (sections_t_C.inst_pos_C sec + 1).
	       inst +\<^sub>p int i \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
	  proof (intro allI impI)
	    fix i
	    assume i_lt: "i < unat (sections_t_C.inst_pos_C sec + 1)"
	    have i_cap: "i < unat inst_cap"
	      using i_lt inst_suc_unat inst_suc_room by linarith
	    show "inst +\<^sub>p int i \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
	      by (rule bufs_disjoint_int_uintD[OF inst_addr i_cap addr_byte_room_nat])
	  qed
	  have addr_varint_data_disj:
	    "\<forall>k < unat (sections_t_C.data_pos_C sec + pend_len). \<forall>i.
	      i < an \<longrightarrow>
	      data +\<^sub>p int k \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat (sections_t_C.data_pos_C sec + pend_len)"
	      and i_lt: "i < an"
	    have k_cap: "k < unat data_cap"
	      using k_lt data_pend_unat data_pend_room by linarith
	    show "data +\<^sub>p int k \<noteq>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	      by (rule bufs_disjoint_word_range_rightD_word[
	        OF data_addr k_cap i_lt addr_an_no_overflow addr_an_room])
	  qed
		  have addr_varint_inst_disj:
		    "\<forall>k < unat (sections_t_C.inst_pos_C sec + 1). \<forall>i.
		      i < an \<longrightarrow>
		      inst +\<^sub>p int k \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
		  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat (sections_t_C.inst_pos_C sec + 1)"
	      and i_lt: "i < an"
	    have k_cap: "k < unat inst_cap"
	      using k_lt inst_suc_unat inst_suc_room by linarith
	    show "inst +\<^sub>p int k \<noteq>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
		      by (rule bufs_disjoint_word_range_rightD_word[
		        OF inst_addr k_cap i_lt addr_an_no_overflow addr_an_room])
		  qed
	  have src_inst_byte_disj:
	    "\<forall>i < unat src_len.
	       src +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
	    by (auto intro!: bufs_disjoint_int_uintD[
	          OF src_inst_disj _ inst_byte_room_nat])
	  have tgt_inst_byte_disj:
	    "\<forall>i < unat tgt_len.
	       tgt +\<^sub>p int i \<noteq> inst +\<^sub>p uint (sections_t_C.inst_pos_C sec)"
	    by (auto intro!: bufs_disjoint_int_uintD[
	          OF tgt_inst_disj _ inst_byte_room_nat])
	  have src_data_write_disj:
	    "\<forall>k < unat src_len. \<forall>i.
	      i < pend_len \<longrightarrow>
	      src +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat src_len" and i_lt: "i < pend_len"
	    show "src +\<^sub>p int k \<noteq>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	      by (rule bufs_disjoint_word_range_rightD_word[
	        OF src_data_disj k_lt i_lt data_pend_no_overflow data_pend_room])
	  qed
	  have tgt_data_write_disj:
	    "\<forall>k < unat tgt_len. \<forall>i.
	      i < pend_len \<longrightarrow>
	      tgt +\<^sub>p int k \<noteq> data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat tgt_len" and i_lt: "i < pend_len"
	    show "tgt +\<^sub>p int k \<noteq>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	      by (rule bufs_disjoint_word_range_rightD_word[
	        OF tgt_data_disj k_lt i_lt data_pend_no_overflow data_pend_room])
	  qed
	  have src_addr_byte_disj:
	    "\<forall>i < unat src_len.
	       src +\<^sub>p int i \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
	    by (auto intro!: bufs_disjoint_int_uintD[
	          OF src_addr_disj _ addr_byte_room_nat])
	  have tgt_addr_byte_disj:
	    "\<forall>i < unat tgt_len.
	       tgt +\<^sub>p int i \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec)"
	    by (auto intro!: bufs_disjoint_int_uintD[
	          OF tgt_addr_disj _ addr_byte_room_nat])
	  have src_addr_write_disj:
	    "\<forall>k < unat src_len. \<forall>i.
	      i < an \<longrightarrow>
	      src +\<^sub>p int k \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat src_len" and i_lt: "i < an"
	    show "src +\<^sub>p int k \<noteq>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	      by (rule bufs_disjoint_word_range_rightD_word[
	        OF src_addr_disj k_lt i_lt addr_an_no_overflow addr_an_room])
	  qed
	  have tgt_addr_write_disj:
	    "\<forall>k < unat tgt_len. \<forall>i.
	      i < an \<longrightarrow>
	      tgt +\<^sub>p int k \<noteq> addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	  proof (intro allI impI)
	    fix k i
	    assume k_lt: "k < unat tgt_len" and i_lt: "i < an"
	    show "tgt +\<^sub>p int k \<noteq>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	      by (rule bufs_disjoint_word_range_rightD_word[
	        OF tgt_addr_disj k_lt i_lt addr_an_no_overflow addr_an_room])
	  qed
	  have src_data_write_disj_unat:
	    "\<And>k i. \<lbrakk>k < unat src_len; unat i < unat pend_len\<rbrakk> \<Longrightarrow>
	      src +\<^sub>p int k \<noteq>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	    using src_data_write_disj by (simp add: word_less_nat_alt)
	  have tgt_data_write_disj_unat:
	    "\<And>k i. \<lbrakk>k < unat tgt_len; unat i < unat pend_len\<rbrakk> \<Longrightarrow>
	      tgt +\<^sub>p int k \<noteq>
	      data +\<^sub>p uint (sections_t_C.data_pos_C sec + i)"
	    using tgt_data_write_disj by (simp add: word_less_nat_alt)
	  have addr_prefix_disj_unat:
	    "\<And>k i. \<lbrakk>k < unat (sections_t_C.addr_pos_C sec);
	      unat i < unat an\<rbrakk> \<Longrightarrow>
	      addr +\<^sub>p int k \<noteq>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	    using addr_prefix_disj_word by (simp add: word_less_nat_alt)
	  have src_addr_write_disj_unat:
	    "\<And>k i. \<lbrakk>k < unat src_len; unat i < unat an\<rbrakk> \<Longrightarrow>
	      src +\<^sub>p int k \<noteq>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	    using src_addr_write_disj by (simp add: word_less_nat_alt)
	  have tgt_addr_write_disj_unat:
	    "\<And>k i. \<lbrakk>k < unat tgt_len; unat i < unat an\<rbrakk> \<Longrightarrow>
	      tgt +\<^sub>p int k \<noteq>
	      addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
	    using tgt_addr_write_disj by (simp add: word_less_nat_alt)
			  note loop_frame_facts =
			    src_heap0 tgt_heap0 src_len_eq tgt_len_eq sec_ok tp_le_nat pend_cap
		    data_pos_le inst_pos_le addr_pos_le data_slack inst_slack addr_slack
	    src_valid tgt_valid pending_valid data_valid inst_valid addr_valid
	    pending_dist data_dist inst_dist addr_dist pending_src pending_tgt
	    pending_data pending_inst pending_addr data_src data_tgt data_inst
	    data_addr inst_src inst_tgt inst_addr addr_src addr_tgt an_le5
	    inst_byte_room_nat inst_byte_room data_pend_room data_pend_no_overflow
	    addr_an_room addr_an_no_overflow inst_suc_room inst_suc_dist
	    inst_suc_unat inst_byte_ptr data_fits addr_fits data_write_valid
	    data_pend_unat pending_write_valid addr_write_valid addr_byte_room_nat
	    addr_byte_room addr_suc_room addr_suc_dist addr_byte_ptr
	    addr_write_inj addr_prefix_disj src_inst_disj tgt_inst_disj
	    src_data_disj tgt_data_disj src_addr_disj tgt_addr_disj
	    data_pending_disj_buf inst_data_disj addr_data_disj addr_inst_disj
		    inst_byte_data_disj inst_byte_addr_disj inst_byte_pending_disj
		    data_pending_disj data_inj data_prefix_disj data_inst_disj
			    data_addr_disj addr_byte_data_disj addr_byte_inst_disj
			    addr_varint_data_disj addr_varint_inst_disj
			    src_inst_byte_disj tgt_inst_byte_disj src_data_write_disj
			    tgt_data_write_disj src_addr_byte_disj tgt_addr_byte_disj
			    src_addr_write_disj tgt_addr_write_disj
			  have copy_ge_nat: "4 \<le> unat (match_t_C.len_C m)"
			    using copy_ge by (simp add: word_le_nat_alt)
			  have copy_gt6_ne4:
			    "6 < unat (match_t_C.len_C m) \<Longrightarrow>
			      match_t_C.len_C m \<noteq> (4 :: 32 word)"
			    by auto
			  have len_nonzero_nat: "unat (match_t_C.len_C m) \<noteq> 0"
			    using copy_ge_nat by simp
		  have match_valid0:
		    "match_valid src_bytes tgt_bytes (unat tp)
		      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
		    using match_rel match tp_lt
		    by (simp add: encode_window_match_rel_def word_less_nat_alt
		                  word_le_nat_alt)
		  have tp_len_room_nat:
		    "unat tp + unat (match_t_C.len_C m) \<le> unat tgt_len"
		    using match_validD(2)[OF match_valid0 len_nonzero_nat] tgt_len_eq
		    by simp
		  have tp_len_no_overflow:
		    "unat tp + unat (match_t_C.len_C m) < 2 ^ 32"
		    using tp_len_room_nat unat_lt2p[of tgt_len] by simp
		  have tp_len_unat:
		    "unat (tp + match_t_C.len_C m) =
		      unat tp + unat (match_t_C.len_C m)"
		    by (rule unat_word_add_no_overflow[OF tp_len_no_overflow])
		  have tp_len_le_nat:
		    "unat (tp + match_t_C.len_C m) \<le> unat tgt_len"
		    using tp_len_room_nat tp_len_unat by simp
		  have tp_len_progress:
		    "unat tp < unat (tp + match_t_C.len_C m)"
		    using copy_ge_nat tp_len_unat by simp
		  have measure_progress:
		    "unat tgt_len - unat (tp + match_t_C.len_C m) <
		      unat tgt_len - unat tp"
		    using tp_len_le_nat tp_len_progress by linarith
		  have addr_an_unat:
		    "unat (sections_t_C.addr_pos_C sec + an) =
		      unat (sections_t_C.addr_pos_C sec) + unat an"
		    by (rule unat_word_add_no_overflow[OF addr_an_no_overflow])
		  have addr_suc_unat:
		    "unat (sections_t_C.addr_pos_C sec + 1) =
		      Suc (unat (sections_t_C.addr_pos_C sec))"
		    using addr_suc_room unat_lt2p[of addr_cap] by unat_arith
		  have add_copy_opcode_bm:
		    "\<And>st add_sz copy_sz. \<lbrakk>
		       (1 :: 32 word) \<le> add_sz; add_sz \<le> (4 :: 32 word);
		       (4 :: 32 word) \<le> copy_sz;
		       mode_t_C.mode_C bm \<le> (5 :: 32 word) \<Longrightarrow>
		         copy_sz \<le> (6 :: 32 word);
		       \<not> mode_t_C.mode_C bm \<le> (5 :: 32 word) \<Longrightarrow>
		         copy_sz = (4 :: 32 word)
		     \<rbrakk> \<Longrightarrow>
		       add_copy_opcode' add_sz copy_sz (mode_t_C.mode_C bm) \<bullet> st
		        \<lbrace> \<lambda>r t.
		            r = Result
		              (if mode_t_C.mode_C bm \<le> (5 :: 32 word) then
		                 163 + mode_t_C.mode_C bm * 12 +
		                   (add_sz - 1) * 3 + (copy_sz - 4)
		               else
		                 235 + (mode_t_C.mode_C bm - 6) * 4 +
		                   (add_sz - 1)) \<and>
		            t = st \<rbrace>"
		  proof -
		    fix st add_sz copy_sz
		    assume add_ge: "(1 :: 32 word) \<le> add_sz"
		      and add_le: "add_sz \<le> (4 :: 32 word)"
		      and copy_ge': "(4 :: 32 word) \<le> copy_sz"
		      and copy_le_if:
		        "mode_t_C.mode_C bm \<le> (5 :: 32 word) \<Longrightarrow>
		          copy_sz \<le> (6 :: 32 word)"
		      and copy_eq_if:
		        "\<not> mode_t_C.mode_C bm \<le> (5 :: 32 word) \<Longrightarrow>
		          copy_sz = (4 :: 32 word)"
		    show "add_copy_opcode' add_sz copy_sz (mode_t_C.mode_C bm) \<bullet> st
		      \<lbrace> \<lambda>r t.
		          r = Result
		            (if mode_t_C.mode_C bm \<le> (5 :: 32 word) then
		               163 + mode_t_C.mode_C bm * 12 +
		                 (add_sz - 1) * 3 + (copy_sz - 4)
		             else
		               235 + (mode_t_C.mode_C bm - 6) * 4 +
		                 (add_sz - 1)) \<and>
		          t = st \<rbrace>"
		    proof (cases "mode_t_C.mode_C bm \<le> (5 :: 32 word)")
		      case True
		      show ?thesis
		        apply (rule runs_to_weaken[
		          OF add_copy_opcode'_mode_le5[
		            OF add_ge add_le True copy_ge' copy_le_if[OF True]]])
		        using True by simp
		    next
		      case False
		      have mode_gt: "(5 :: 32 word) < mode_t_C.mode_C bm"
		        using False by (simp add: word_less_nat_alt word_le_nat_alt)
		      have copy_eq': "copy_sz = (4 :: 32 word)"
		        by (rule copy_eq_if[OF False])
		      show ?thesis
		        apply (rule runs_to_weaken[
		          OF add_copy_opcode'_mode_gt5[
		            OF add_ge add_le mode_gt mode_le8 copy_eq']])
		        using False by simp
		    qed
		  qed
	  note gets_the_best_mode'_result[OF bm, runs_to_vcg]
	  note gets_the_best_mode'_result[runs_to_vcg]
	  note add_copy_opcode_bm[runs_to_vcg]
  have write_byte_src_tgt_cache:
    "\<And>s c buf cap pos b. \<lbrakk>
       enc_cache_abs s c; enc_cache_wf c; pos < cap;
       ptr_valid (heap_typing s) (buf +\<^sub>p uint pos);
       \<forall>i < unat src_len. src +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos;
       \<forall>i < unat tgt_len. tgt +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos
     \<rbrakk> \<Longrightarrow>
       write_byte' buf cap pos b \<bullet> s
        \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                heap_bytes t src (unat src_len) =
                  heap_bytes s src (unat src_len) \<and>
                heap_bytes t tgt (unat tgt_len) =
                  heap_bytes s tgt (unat tgt_len) \<and>
                enc_cache_abs t c \<and> enc_cache_wf c \<and>
                heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_success_preserves_heap_bytes2_cache_abs)
  have write_bytes_src_tgt_cache:
    "\<And>s c buf cap pos inbuf src_off len. \<lbrakk>
       enc_cache_abs s c; enc_cache_wf c; \<not> cap - pos < len;
       \<forall>j < unat len.
         ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j));
       \<forall>j < unat len.
         ptr_valid (heap_typing s) (inbuf +\<^sub>p uint (src_off + of_nat j));
       \<forall>k < unat src_len. \<forall>i.
         i < len \<longrightarrow> src +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i);
       \<forall>k < unat tgt_len. \<forall>i.
         i < len \<longrightarrow> tgt +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)
     \<rbrakk> \<Longrightarrow>
       write_bytes' buf cap pos inbuf src_off len \<bullet> s
        \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                heap_bytes t src (unat src_len) =
                  heap_bytes s src (unat src_len) \<and>
                heap_bytes t tgt (unat tgt_len) =
                  heap_bytes s tgt (unat tgt_len) \<and>
                enc_cache_abs t c \<and> enc_cache_wf c \<and>
                heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_preserves_heap_bytes2_cache_abs)
  have write_varint_src_tgt_cache:
    "\<And>s c buf cap pos v n. \<lbrakk>
       enc_cache_abs s c; enc_cache_wf c; varint_size' v s = Some n;
       \<not> cap - pos < n;
       \<forall>j < unat n.
         ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j));
       \<forall>k < unat src_len. \<forall>i.
         i < n \<longrightarrow> src +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i);
       \<forall>k < unat tgt_len. \<forall>i.
         i < n \<longrightarrow> tgt +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)
     \<rbrakk> \<Longrightarrow>
       write_varint' buf cap pos v \<bullet> s
        \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                heap_bytes t src (unat src_len) =
                  heap_bytes s src (unat src_len) \<and>
                heap_bytes t tgt (unat tgt_len) =
                  heap_bytes s tgt (unat tgt_len) \<and>
                enc_cache_abs t c \<and> enc_cache_wf c \<and>
                heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes2_cache_abs)
  have write_varint_bm_an_src_tgt_cache:
    "\<And>s c buf cap pos. \<lbrakk>
       enc_cache_abs s c; enc_cache_wf c;
       varint_size' (mode_t_C.arg_C bm) s = Some an;
       \<not> cap - pos < an;
       \<forall>j < unat an.
         ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j));
       \<forall>k < unat src_len. \<forall>i.
         i < an \<longrightarrow> src +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i);
       \<forall>k < unat tgt_len. \<forall>i.
         i < an \<longrightarrow> tgt +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)
     \<rbrakk> \<Longrightarrow>
       write_varint' buf cap pos (mode_t_C.arg_C bm) \<bullet> s
        \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + an) ENC_OK) \<and>
                heap_bytes t src (unat src_len) =
                  heap_bytes s src (unat src_len) \<and>
                heap_bytes t tgt (unat tgt_len) =
                  heap_bytes s tgt (unat tgt_len) \<and>
                enc_cache_abs t c \<and> enc_cache_wf c \<and>
                heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes2_cache_abs)
  have emit_address_byte_src_tgt_cache:
    "\<And>s c addr_buf addr_cap addr_pos mode. \<lbrakk>
       enc_cache_abs s c; enc_cache_wf c;
       \<not> mode_t_C.mode_C mode < (6 :: 32 word);
       addr_pos < addr_cap;
       ptr_valid (heap_typing s) (addr_buf +\<^sub>p uint addr_pos);
       ptr_range_distinct addr_buf (Suc (unat addr_pos));
       \<forall>i < unat src_len. src +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint addr_pos;
       \<forall>i < unat tgt_len. tgt +\<^sub>p int i \<noteq> addr_buf +\<^sub>p uint addr_pos
     \<rbrakk> \<Longrightarrow>
       emit_address' addr_buf addr_cap addr_pos mode \<bullet> s
        \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + 1) ENC_OK) \<and>
                heap_bytes t src (unat src_len) =
                  heap_bytes s src (unat src_len) \<and>
                heap_bytes t tgt (unat tgt_len) =
                  heap_bytes s tgt (unat tgt_len) \<and>
                enc_cache_abs t c \<and> enc_cache_wf c \<and>
                heap_typing t = heap_typing s \<rbrace>"
    by (rule emit_address'_success_byte_preserves_heap_bytes2_cache_abs)
	  have emit_address_varint_src_tgt_cache:
	    "\<And>s c addr_buf addr_cap addr_pos mode n. \<lbrakk>
	       enc_cache_abs s c; enc_cache_wf c;
	       mode_t_C.mode_C mode < (6 :: 32 word);
	       varint_size' (mode_t_C.arg_C mode) s = Some n;
       \<not> addr_cap - addr_pos < n;
       \<forall>j < unat n.
         ptr_valid (heap_typing s)
           (addr_buf +\<^sub>p uint (addr_pos + of_nat j));
       \<forall>i < unat n. \<forall>j < unat n.
         i \<noteq> j \<longrightarrow>
         addr_buf +\<^sub>p uint (addr_pos + of_nat i) \<noteq>
         addr_buf +\<^sub>p uint (addr_pos + of_nat j);
       \<forall>k < unat addr_pos. \<forall>i.
         i < n \<longrightarrow>
         addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i);
       unat addr_pos + unat n < 2 ^ 32;
       \<forall>k < unat src_len. \<forall>i.
         i < n \<longrightarrow> src +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i);
       \<forall>k < unat tgt_len. \<forall>i.
         i < n \<longrightarrow> tgt +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i)
     \<rbrakk> \<Longrightarrow>
       emit_address' addr_buf addr_cap addr_pos mode \<bullet> s
        \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + n) ENC_OK) \<and>
                heap_bytes t src (unat src_len) =
                  heap_bytes s src (unat src_len) \<and>
                heap_bytes t tgt (unat tgt_len) =
                  heap_bytes s tgt (unat tgt_len) \<and>
	                enc_cache_abs t c \<and> enc_cache_wf c \<and>
	                heap_typing t = heap_typing s \<rbrace>"
	    by (rule emit_address'_success_varint_preserves_heap_bytes2_cache_abs)
	  have emit_address_bm_an_src_tgt_cache:
	    "\<And>s c addr_buf addr_cap addr_pos. \<lbrakk>
	       enc_cache_abs s c; enc_cache_wf c;
	       mode_t_C.mode_C bm < (6 :: 32 word);
	       varint_size' (mode_t_C.arg_C bm) s = Some an;
	       \<not> addr_cap - addr_pos < an;
	       \<forall>j < unat an.
	         ptr_valid (heap_typing s)
	           (addr_buf +\<^sub>p uint (addr_pos + of_nat j));
	       \<forall>i < unat an. \<forall>j < unat an.
	         i \<noteq> j \<longrightarrow>
	         addr_buf +\<^sub>p uint (addr_pos + of_nat i) \<noteq>
	         addr_buf +\<^sub>p uint (addr_pos + of_nat j);
	       \<forall>k < unat addr_pos. \<forall>i.
	         i < an \<longrightarrow>
	         addr_buf +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i);
	       unat addr_pos + unat an < 2 ^ 32;
	       \<forall>k < unat src_len. \<forall>i.
	         i < an \<longrightarrow> src +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i);
	       \<forall>k < unat tgt_len. \<forall>i.
	         i < an \<longrightarrow> tgt +\<^sub>p int k \<noteq> addr_buf +\<^sub>p uint (addr_pos + i)
	     \<rbrakk> \<Longrightarrow>
	       emit_address' addr_buf addr_cap addr_pos bm \<bullet> s
	        \<lbrace> \<lambda>r t. r = Result (wr_t_C (addr_pos + an) ENC_OK) \<and>
	                heap_bytes t src (unat src_len) =
	                  heap_bytes s src (unat src_len) \<and>
	                heap_bytes t tgt (unat tgt_len) =
	                  heap_bytes s tgt (unat tgt_len) \<and>
	                enc_cache_abs t c \<and> enc_cache_wf c \<and>
	                heap_typing t = heap_typing s \<rbrace>"
	    by (rule emit_address'_success_varint_preserves_heap_bytes2_cache_abs)
	  have cache_update_src_tgt_cache:
	    "\<And>s c copy_addr. \<lbrakk>enc_cache_abs s c; enc_cache_wf c\<rbrakk> \<Longrightarrow>
	       cache_update' copy_addr \<bullet> s
	        \<lbrace> \<lambda>r t. r = Result () \<and>
                heap_bytes t src (unat src_len) =
                  heap_bytes s src (unat src_len) \<and>
                heap_bytes t tgt (unat tgt_len) =
                  heap_bytes s tgt (unat tgt_len) \<and>
                enc_cache_abs t (cache_update c (unat copy_addr)) \<and>
	                enc_cache_wf (cache_update c (unat copy_addr)) \<and>
		                heap_typing t = heap_typing s \<rbrace>"
	    by (rule cache_update'_preserves_heap_bytes2_enc_cache_abs_wf)
		  have ptr_valid_heap_typing_eq:
		    "\<And>t p. heap_typing t = heap_typing s \<Longrightarrow>
		      ptr_valid (heap_typing s) p \<Longrightarrow> ptr_valid (heap_typing t) p"
		    by simp
		  have data_write_valid_t:
		    "\<And>t j. heap_typing t = heap_typing s \<Longrightarrow>
		      j < unat pend_len \<Longrightarrow>
		      IS_VALID(8 word) t
		        (data +\<^sub>p uint (sections_t_C.data_pos_C sec + of_nat j))"
		    using data_write_valid by simp
		  have pending_write_valid_t:
		    "\<And>t j. heap_typing t = heap_typing s \<Longrightarrow>
		      j < unat pend_len \<Longrightarrow>
		      IS_VALID(8 word) t (pending +\<^sub>p uint (of_nat j :: 32 word))"
		    using pending_write_valid by simp
		  have addr_write_valid_ta:
		    "\<And>t ta j. heap_typing t = heap_typing s \<Longrightarrow>
		      heap_typing ta = heap_typing t \<Longrightarrow>
		      j < unat an \<Longrightarrow>
		      IS_VALID(8 word) ta
		        (addr +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
		    using addr_write_valid by simp
	  note write_byte_src_tgt_spec_cache =
	    write_byte_src_tgt_cache[where c = "enc_cache spec_st"]
	  note write_bytes_src_tgt_spec_cache =
	    write_bytes_src_tgt_cache[where c = "enc_cache spec_st"]
	  note write_varint_bm_an_src_tgt_spec_cache =
	    write_varint_bm_an_src_tgt_cache[where c = "enc_cache spec_st"]
	  note emit_address_byte_src_tgt_spec_cache =
	    emit_address_byte_src_tgt_cache[where c = "enc_cache spec_st"]
	  note emit_address_bm_an_src_tgt_spec_cache =
	    emit_address_bm_an_src_tgt_cache[where c = "enc_cache spec_st"]
		  note cache_update_src_tgt_spec_cache =
		    cache_update_src_tgt_cache[where c = "enc_cache spec_st"]
		  let ?Post =
		    "\<lambda>r t. \<exists>sec' tp' pend_len' spec_st''.
		      r = Result (pend_len', sec', tp') \<and>
		      encode_window_loop_rel t src src_len tgt tgt_len
		        data data_cap inst inst_cap addr addr_cap pending pending_cap
		        sec' tp' pend_len' src_bytes tgt_bytes spec_st'' \<and>
		      enc_tp spec_st < enc_tp spec_st'' \<and>
		      (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
		        measure
		          (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
		             unat tgt_len - unat tp)"
				  have low_branch:
				    "unat (mode_t_C.mode_C bm) \<le> 5 \<Longrightarrow>
				      encode_window_c_match_branch src_len
				        data data_cap inst inst_cap addr addr_cap
				        pending pend_len sec tp m \<bullet> s \<lbrace> ?Post \<rbrace>"
				  proof -
				    assume True: "unat (mode_t_C.mode_C bm) \<le> 5"
				    have True_word: "mode_t_C.mode_C bm \<le> (5 :: 32 word)"
				      using True by (simp add: word_le_nat_alt)
				    note write_byte_src_tgt_spec_cache[runs_to_vcg]
			    note write_bytes_src_tgt_spec_cache[runs_to_vcg]
			    note write_varint_bm_an_src_tgt_spec_cache[runs_to_vcg]
			    note emit_address_byte_src_tgt_spec_cache[runs_to_vcg]
			    note emit_address_bm_an_src_tgt_spec_cache[runs_to_vcg]
			    note cache_update_src_tgt_spec_cache[runs_to_vcg]
			    show ?thesis
		      unfolding encode_window_c_match_branch_def
		      apply runs_to_vcg
		      using rel buffers match_rel tp_lt match match_len fused copy_ge
	      pending_len pend_ge pend_le abs cache_wf bm True True_word
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
	    apply (subst try_emit_add_copy'_def)
    apply runs_to_vcg
		    using assms copy_ge pend_ge pend_le bm mode_le8 addr_size addr_exact
		      addr_exact_le5 addr_exact_gt5 op_nz_le5_gt6 loop_frame_facts
		      True True_word
	    apply -
	    apply (simp add: word_less_nat_alt word_le_nat_alt)
    apply (simp add: word_less_nat_alt word_le_nat_alt)
    apply (simp add: word_less_nat_alt word_le_nat_alt)
	    apply (simp add: word_less_nat_alt word_le_nat_alt)
	    apply (simp add: word_less_nat_alt word_le_nat_alt)
	    apply (simp add: word_less_nat_alt word_le_nat_alt)
	    apply (rule exI[where x = bm])
    apply (simp add: bm word_less_nat_alt word_le_nat_alt)
	     apply (rule runs_to_finally)
	     apply runs_to_vcg
	     apply -
		    apply (simp add: pend_ge True_word)
		     apply (simp add: pend_le)
		    apply (simp add: True_word word_le_nat_alt)
		     apply (simp add: op_nz_le5_gt6 word_le_nat_alt)
	     subgoal
	       apply (rule FalseE)
	       using op_nz_le5_gt6
		    apply (simp add: True_word word_le_nat_alt)
	       done
			    apply (rule inst_byte_room)
			    subgoal for i
			      by (rule src_inst_byte_disj[rule_format], assumption)
			    subgoal for i
			      by (rule tgt_inst_byte_disj[rule_format], assumption)
		     apply (rule data_fits)
			        subgoal for st j
			          using data_write_valid[rule_format, of j] by simp
     subgoal for st j
       using pending_write_valid[rule_format, of j] by simp
	     subgoal for st k i
	       using src_data_write_disj[rule_format, of k i]
	       by (simp add: word_less_nat_alt)
		     subgoal for st k i
		       using tgt_data_write_disj[rule_format, of k i]
		       by (simp add: word_less_nat_alt)
	     apply (simp add: word_less_nat_alt word_le_nat_alt)
     apply (simp add: word_less_nat_alt)
     apply (simp add: addr_write_valid)
     apply (simp add: tgt_addr_write_disj word_less_nat_alt)
     apply (simp add: sec_ok)
     apply (simp add: src_addr_write_disj word_less_nat_alt)
     apply (subst varint_size'_state_independent[where s = s])
     apply (rule addr_size)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_sub)
     subgoal for t ta j
       using addr_write_valid[rule_format, of j] by simp
     subgoal for t ta i j
       using addr_write_inj_nat[of i j] by simp
     subgoal for t ta k i
       using addr_prefix_disj_word[of k i] by simp
	    subgoal
	      using src_addr_write_disj by auto
	    subgoal
	      using tgt_addr_write_disj by auto
	     apply (simp add: sec_ok)
	     defer
	     apply (simp add: word_less_nat_alt; linarith)
		    subgoal
		      using src_inst_byte_disj by blast
		    subgoal
		      by (rule mode_nat_le5_not_word_le_contra; assumption)
		    apply (simp add: pend_ge True_word)
		    subgoal
		      by (rule mode_nat_le5_not_word_le_contra; assumption)
		    apply (simp add: True_word word_le_nat_alt)
	    subgoal
	      using src_data_write_disj[rule_format]
	      by (simp add: word_less_nat_alt)
	    subgoal
	      by (rule mode_nat_le5_not_word_le_contra; assumption)
	     subgoal
	       using src_data_write_disj[rule_format] tgt_data_write_disj[rule_format]
	       by (auto intro: data_write_valid_t pending_write_valid_t
	            simp: word_less_nat_alt word_le_nat_alt)
	     subgoal
	       using src_data_write_disj[rule_format] tgt_data_write_disj[rule_format]
	       by (auto intro: data_write_valid_t pending_write_valid_t
	            simp: word_less_nat_alt word_le_nat_alt)
	     subgoal
	       using src_data_write_disj[rule_format] tgt_data_write_disj[rule_format]
	       by (auto intro: data_write_valid_t pending_write_valid_t
	            simp: word_less_nat_alt word_le_nat_alt)
	     subgoal
	       using src_data_write_disj[rule_format] tgt_data_write_disj[rule_format]
	       by (auto intro: data_write_valid_t pending_write_valid_t
	            simp: word_less_nat_alt word_le_nat_alt)
     apply (simp add: word_less_nat_alt word_le_nat_alt)
     apply (simp add: word_less_nat_alt)
	     apply (simp add: addr_write_valid)
		     apply (simp add: tgt_addr_write_disj word_less_nat_alt)
	    apply (simp add: sec_ok)
	    apply (simp add: src_addr_write_disj word_less_nat_alt)
		    subgoal
		      using src_addr_write_disj[rule_format] tgt_addr_write_disj[rule_format]
		      by (auto intro: addr_size_any
		            simp: word_less_nat_alt word_le_nat_alt)
		    subgoal
		      using src_addr_write_disj[rule_format] tgt_addr_write_disj[rule_format]
		      by (auto intro: addr_size_any
		            simp: word_less_nat_alt word_le_nat_alt)
		     apply (simp add: sec_ok)
		     subgoal
		       by (simp add: True_word word_less_nat_alt word_le_nat_alt)
		     subgoal
		       by (simp add: True_word word_less_nat_alt word_le_nat_alt)
	     apply (simp add: word_less_nat_alt word_le_nat_alt)
	     apply (simp add: word_less_nat_alt word_le_nat_alt)
	     apply (simp add: word_less_nat_alt word_le_nat_alt)
	    apply (simp add: word_less_nat_alt word_le_nat_alt)
	    apply (simp add: word_less_nat_alt word_le_nat_alt)
	    apply (simp add: word_less_nat_alt word_le_nat_alt)
					    subgoal
					      apply (rule exI[where x = bm])
					      apply (simp add: bm)
					      apply (rule runs_to_finally)
					      apply runs_to_vcg
							      apply -
								      apply (simp_all add: condition_def
									        sections_result_def
									        word_less_nat_alt word_le_nat_alt
								        sec_ok addr_size_any op_nz_le5_le6 op_nz_le5_gt6
								        op_d2_nz_gt5 op_d2_nz_gt5_nat op_gt5_nz_nat
								        mode_gt5_not_lt6_nat
								        fused_t_C.fused_C.fused_C_def
								        fused_t_C.s_C.s_C_def)
									      subgoal premises prems
				      proof -
							        let ?sec_f =
							          "addr_pos_C_update (\<lambda>_. addr_pos_C sec + an)
						            (inst_pos_C_update (\<lambda>_. inst_pos_C sec + 1)
						              (data_pos_C_update
						                (\<lambda>_. data_pos_C sec + pend_len) sec))"
				        let ?c1 =
				          "cache_update (enc_cache spec_st)
				            (unat (match_t_C.pos_C m))"
				        have data_room_fused:
				          "unat (sections_t_C.data_pos_C ?sec_f) +
				            (unat tgt_len -
				              unat (tp + match_t_C.len_C m)) + 64
				            \<le> unat data_cap"
				          using data_slack data_pend_unat tp_len_unat
				            tp_len_le_nat
				          by (simp; linarith)
				        have inst_room_fused:
				          "unat (sections_t_C.inst_pos_C ?sec_f) +
				            (unat tgt_len -
				              unat (tp + match_t_C.len_C m)) + 64
				            \<le> unat inst_cap"
				          using inst_slack inst_suc_unat pend_ge_nat
				            tp_len_unat tp_len_le_nat copy_ge_nat
				          by (simp; linarith)
				        have addr_room_fused:
				          "unat (sections_t_C.addr_pos_C ?sec_f) +
				            (unat tgt_len -
				              unat (tp + match_t_C.len_C m)) + 64
				            \<le> unat addr_cap"
				          using addr_slack addr_an_unat an_le5 pend_ge_nat
				            tp_len_unat tp_len_le_nat copy_ge_nat
				          by (simp; linarith)
					        have loop_progress_any:
					          "\<And>st. \<lbrakk>
					            heap_bytes st src (unat src_len) = src_bytes;
					            heap_bytes st tgt (unat tgt_len) = tgt_bytes;
					            enc_cache_abs st ?c1; enc_cache_wf ?c1\<rbrakk> \<Longrightarrow>
					            \<exists>spec_st''. encode_window_loop_rel st
					              src src_len tgt tgt_len data data_cap
					              inst inst_cap addr addr_cap pending pending_cap
					              ?sec_f (tp + match_t_C.len_C m) 0
					              src_bytes tgt_bytes spec_st'' \<and>
					              enc_tp spec_st < enc_tp spec_st'' \<and>
					              unat tgt_len - unat (tp + match_t_C.len_C m)
					                < unat tgt_len - unat tp"
					        proof -
					          fix st
					          assume st_src:
					              "heap_bytes st src (unat src_len) = src_bytes"
					            and st_tgt:
					              "heap_bytes st tgt (unat tgt_len) = tgt_bytes"
					            and st_abs: "enc_cache_abs st ?c1"
					            and st_wf: "enc_cache_wf ?c1"
					          have loop_ex:
					            "\<exists>spec_st''. encode_window_loop_rel st
					              src src_len tgt tgt_len data data_cap
					              inst inst_cap addr addr_cap pending pending_cap
					              ?sec_f (tp + match_t_C.len_C m) 0
					              src_bytes tgt_bytes spec_st''"
					            apply (rule encode_window_loop_rel_zero_pending_witness[
					              where c = ?c1])
					            subgoal by (rule st_src)
					            subgoal by (rule st_tgt)
					            subgoal by (rule src_len_eq)
					            subgoal by (rule tgt_len_eq)
					            subgoal using sec_ok by simp
					            subgoal using tp_len_le_nat by simp
					            subgoal using data_room_fused by (simp; linarith)
					            subgoal using inst_room_fused by (simp; linarith)
					            subgoal using addr_room_fused by (simp; linarith)
					            subgoal using data_room_fused by simp
					            subgoal using inst_room_fused by simp
					            subgoal using addr_room_fused by simp
					            subgoal by (rule st_abs)
					            subgoal by (rule st_wf)
					            done
					          then obtain spec_st'' where loop_rel_st:
					            "encode_window_loop_rel st
					              src src_len tgt tgt_len data data_cap
					              inst inst_cap addr addr_cap pending pending_cap
					              ?sec_f (tp + match_t_C.len_C m) 0
					              src_bytes tgt_bytes spec_st''"
					            by blast
					          have enc_tp_less:
					            "enc_tp spec_st < enc_tp spec_st''"
					            using rel loop_rel_st tp_len_progress
					            by (simp add: encode_window_loop_rel_def)
					          have measure_rel:
					            "unat tgt_len - unat (tp + match_t_C.len_C m)
					              < unat tgt_len - unat tp"
					            using measure_progress by simp
					          show "\<exists>spec_st''. encode_window_loop_rel st
					              src src_len tgt tgt_len data data_cap
					              inst inst_cap addr addr_cap pending pending_cap
					              ?sec_f (tp + match_t_C.len_C m) 0
					              src_bytes tgt_bytes spec_st'' \<and>
					              enc_tp spec_st < enc_tp spec_st'' \<and>
					              unat tgt_len - unat (tp + match_t_C.len_C m)
					                < unat tgt_len - unat tp"
					            using loop_rel_st enc_tp_less measure_rel by blast
					        qed
						        show ?thesis
						          using prems loop_progress_any by blast
							      qed
								    done
									      (*
									      subgoal premises prems
							        using prems spec_mode_gt5_copy_ne4_false_nat by blast
						      subgoal premises prems
						      proof -
						        let ?sec_f =
						          "addr_pos_C_update (\<lambda>_. addr_pos_C sec + an)
						            (inst_pos_C_update (\<lambda>_. inst_pos_C sec + 1)
						              (data_pos_C_update
						                (\<lambda>_. data_pos_C sec + pend_len) sec))"
						        let ?c1 =
						          "cache_update (enc_cache spec_st)
						            (unat (match_t_C.pos_C m))"
						        have len4:
						          "match_t_C.len_C m = (4 :: 32 word)"
						          using prems by simp
						        have tp4_eq:
						          "tp + (4 :: 32 word) = tp + match_t_C.len_C m"
						          using len4 by simp
						        have data_room_fused:
						          "unat (sections_t_C.data_pos_C ?sec_f) +
						            (unat tgt_len -
						              unat (tp + (4 :: 32 word))) + 64
						            \<le> unat data_cap"
						          using data_slack data_pend_unat tp_len_unat
						            tp_len_le_nat tp4_eq
						          by (simp; linarith)
						        have inst_room_fused:
						          "unat (sections_t_C.inst_pos_C ?sec_f) +
						            (unat tgt_len -
						              unat (tp + (4 :: 32 word))) + 64
						            \<le> unat inst_cap"
						          using inst_slack inst_suc_unat pend_ge_nat
						            tp_len_unat tp_len_le_nat copy_ge_nat tp4_eq
						          by (simp; linarith)
						        have addr_room_fused:
						          "unat (sections_t_C.addr_pos_C ?sec_f) +
						            (unat tgt_len -
						              unat (tp + (4 :: 32 word))) + 64
						            \<le> unat addr_cap"
						          using addr_slack addr_an_unat an_le5 pend_ge_nat
						            tp_len_unat tp_len_le_nat copy_ge_nat tp4_eq
						          by (simp; linarith)
						        have loop_progress_any:
						          "\<And>st. \<lbrakk>
						            heap_bytes st src (unat src_len) = src_bytes;
						            heap_bytes st tgt (unat tgt_len) = tgt_bytes;
						            enc_cache_abs st ?c1; enc_cache_wf ?c1\<rbrakk> \<Longrightarrow>
						            \<exists>spec_st''. encode_window_loop_rel st
						              src src_len tgt tgt_len data data_cap
						              inst inst_cap addr addr_cap pending pending_cap
						              ?sec_f (tp + (4 :: 32 word)) 0
						              src_bytes tgt_bytes spec_st'' \<and>
						              enc_tp spec_st < enc_tp spec_st'' \<and>
						              unat tgt_len - unat (tp + (4 :: 32 word))
						                < unat tgt_len - unat tp"
						        proof -
						          fix st
						          assume st_src:
						              "heap_bytes st src (unat src_len) = src_bytes"
						            and st_tgt:
						              "heap_bytes st tgt (unat tgt_len) = tgt_bytes"
						            and st_abs: "enc_cache_abs st ?c1"
						            and st_wf: "enc_cache_wf ?c1"
						          have loop_ex:
						            "\<exists>spec_st''. encode_window_loop_rel st
						              src src_len tgt tgt_len data data_cap
						              inst inst_cap addr addr_cap pending pending_cap
						              ?sec_f (tp + (4 :: 32 word)) 0
						              src_bytes tgt_bytes spec_st''"
						            apply (rule encode_window_loop_rel_zero_pending_witness[
						              where c = ?c1])
						            subgoal by (rule st_src)
						            subgoal by (rule st_tgt)
						            subgoal by (rule src_len_eq)
						            subgoal by (rule tgt_len_eq)
						            subgoal using sec_ok by simp
						            subgoal using tp_len_le_nat tp4_eq by simp
						            subgoal using data_room_fused by (simp; linarith)
						            subgoal using inst_room_fused by (simp; linarith)
						            subgoal using addr_room_fused by (simp; linarith)
						            subgoal using data_room_fused by simp
						            subgoal using inst_room_fused by simp
						            subgoal using addr_room_fused by simp
						            subgoal by (rule st_abs)
						            subgoal by (rule st_wf)
						            done
						          then obtain spec_st'' where loop_rel_st:
						            "encode_window_loop_rel st
						              src src_len tgt tgt_len data data_cap
						              inst inst_cap addr addr_cap pending pending_cap
						              ?sec_f (tp + (4 :: 32 word)) 0
						              src_bytes tgt_bytes spec_st''"
						            by blast
						          have enc_tp_less:
						            "enc_tp spec_st < enc_tp spec_st''"
						            using rel loop_rel_st tp_len_progress tp4_eq
						            by (simp add: encode_window_loop_rel_def)
						          have measure_rel:
						            "unat tgt_len - unat (tp + (4 :: 32 word))
						              < unat tgt_len - unat tp"
						            using measure_progress tp4_eq by simp
						          show "\<exists>spec_st''. encode_window_loop_rel st
						              src src_len tgt tgt_len data data_cap
						              inst inst_cap addr addr_cap pending pending_cap
						              ?sec_f (tp + (4 :: 32 word)) 0
						              src_bytes tgt_bytes spec_st'' \<and>
						              enc_tp spec_st < enc_tp spec_st'' \<and>
						              unat tgt_len - unat (tp + (4 :: 32 word))
						                < unat tgt_len - unat tp"
						            using loop_rel_st enc_tp_less measure_rel by blast
							        qed
							        show ?thesis
							          using prems sec_ok
							          by (clarsimp simp: sections_result_def
							                word_less_nat_alt word_le_nat_alt; linarith)
							      qed
						      subgoal premises prems for t ta taa taaa
						      proof -
						        let ?sec_f =
						          "addr_pos_C_update (\<lambda>_. addr_pos_C sec + an)
						            (inst_pos_C_update (\<lambda>_. inst_pos_C sec + 1)
						              (data_pos_C_update
						                (\<lambda>_. data_pos_C sec + pend_len) sec))"
						        let ?c1 =
						          "cache_update (enc_cache spec_st)
						            (unat (match_t_C.pos_C m))"
						        have len4:
						          "match_t_C.len_C m = (4 :: 32 word)"
						          using prems by simp
						        have tp4_eq:
						          "tp + (4 :: 32 word) = tp + match_t_C.len_C m"
						          using len4 by simp
						        have data_room_fused:
						          "unat (sections_t_C.data_pos_C ?sec_f) +
						            (unat tgt_len -
						              unat (tp + (4 :: 32 word))) + 64
						            \<le> unat data_cap"
						          using data_slack data_pend_unat tp_len_unat
						            tp_len_le_nat tp4_eq
						          by (simp; linarith)
						        have inst_room_fused:
						          "unat (sections_t_C.inst_pos_C ?sec_f) +
						            (unat tgt_len -
						              unat (tp + (4 :: 32 word))) + 64
						            \<le> unat inst_cap"
						          using inst_slack inst_suc_unat pend_ge_nat
						            tp_len_unat tp_len_le_nat copy_ge_nat tp4_eq
						          by (simp; linarith)
						        have addr_room_fused:
						          "unat (sections_t_C.addr_pos_C ?sec_f) +
						            (unat tgt_len -
						              unat (tp + (4 :: 32 word))) + 64
						            \<le> unat addr_cap"
						          using addr_slack addr_an_unat an_le5 pend_ge_nat
						            tp_len_unat tp_len_le_nat copy_ge_nat tp4_eq
						          by (simp; linarith)
						        have loop_ex:
						          "\<exists>spec_st''. encode_window_loop_rel taaa
						            src src_len tgt tgt_len data data_cap
						            inst inst_cap addr addr_cap pending pending_cap
						            ?sec_f (tp + (4 :: 32 word)) 0
						            src_bytes tgt_bytes spec_st''"
						          apply (rule encode_window_loop_rel_zero_pending_witness[
						            where c = ?c1])
						          subgoal using prems by simp
						          subgoal using prems by simp
						          subgoal by (rule src_len_eq)
						          subgoal by (rule tgt_len_eq)
						          subgoal using sec_ok by simp
						          subgoal using tp_len_le_nat tp4_eq by simp
						          subgoal using data_room_fused by (simp; linarith)
						          subgoal using inst_room_fused by (simp; linarith)
						          subgoal using addr_room_fused by (simp; linarith)
						          subgoal using data_room_fused by simp
						          subgoal using inst_room_fused by simp
						          subgoal using addr_room_fused by simp
						          subgoal using prems by simp
						          subgoal using prems by simp
						          done
						        then obtain spec_st'' where loop_rel_taaa:
						          "encode_window_loop_rel taaa
						            src src_len tgt tgt_len data data_cap
						            inst inst_cap addr addr_cap pending pending_cap
						            ?sec_f (tp + (4 :: 32 word)) 0
						            src_bytes tgt_bytes spec_st''"
						          by blast
						        have enc_tp_less:
						          "enc_tp spec_st < enc_tp spec_st''"
						          using rel loop_rel_taaa tp_len_progress tp4_eq
						          by (simp add: encode_window_loop_rel_def)
						        have measure_rel:
						          "unat tgt_len - unat (tp + (4 :: 32 word))
						            < unat tgt_len - unat tp"
						          using measure_progress tp4_eq by simp
						        show ?thesis
						          using loop_rel_taaa enc_tp_less measure_rel by blast
						      qed
							      done
							      *)
						    subgoal premises prems for t ta taa taaa
				    proof -
				      let ?sec_f =
				        "addr_pos_C_update (\<lambda>_. addr_pos_C sec + an)
				          (inst_pos_C_update (\<lambda>_. inst_pos_C sec + 1)
				            (data_pos_C_update
				              (\<lambda>_. data_pos_C sec + pend_len) sec))"
				      let ?c1 =
				        "cache_update (enc_cache spec_st)
				          (unat (match_t_C.pos_C m))"
				      let ?copy_addr = "match_t_C.pos_C m + (6 :: 32 word)"
				      let ?here = "src_len + (tp + (6 :: 32 word))"
				      let ?copy_len = "match_t_C.len_C m - (6 :: 32 word)"
				      have copy_gt6_nat: "6 < unat (match_t_C.len_C m)"
				        using prems by simp
				      have abs_res: "enc_cache_abs taaa ?c1"
				        using prems by simp
				      have wf_res: "enc_cache_wf ?c1"
				        using prems by simp
				      obtain bm_res where bm_res:
				        "best_mode' ?copy_addr ?here taaa = Some bm_res"
				        by (rule best_mode'_some[OF abs_res wf_res])
				      have mode_res_wf:
				        "enc_mode_arg_wf ?c1 ?copy_addr ?here bm_res"
				        by (rule best_mode'_encode_address_correct[
				          OF abs_res wf_res bm_res])
				      have mode_res_le8:
				        "mode_t_C.mode_C bm_res \<le> (8 :: 32 word)"
				        by (rule enc_mode_arg_wf_mode_word_le8[OF mode_res_wf])
				      obtain an_res where an_res:
				        "varint_size' (mode_t_C.arg_C bm_res) taaa =
				          Some an_res"
				        using varint_size'_some by blast
				      obtain sn_res where sn_res:
				        "varint_size' ?copy_len taaa = Some sn_res"
				        using varint_size'_some by blast
				      have pos_len_room_nat:
				        "unat (match_t_C.pos_C m) +
				          unat (match_t_C.len_C m) \<le> unat src_len"
				        using match_validD(1)[OF match_valid0 len_nonzero_nat]
				          src_len_eq by simp
				      have src_len_lt32: "unat src_len < 2 ^ 32"
				        using unat_lt2p[of src_len] by simp
				      have pos_6_no_overflow:
				        "unat (match_t_C.pos_C m) + 6 < 2 ^ 32"
				        using pos_len_room_nat copy_gt6_nat src_len_lt32
				        by linarith
				      have copy_addr_unat:
				        "unat ?copy_addr =
				          unat (match_t_C.pos_C m) + 6"
				        using pos_6_no_overflow
				        by (simp add: unat_word_ariths)
				      have addr_bytes_len_res:
				        "length (enc_best_bytes (mode_t_C.mode_C bm_res)
				          (mode_t_C.arg_C bm_res)) \<le> 1"
				      proof -
				        have exact_res:
				          "encode_address ?c1 (unat ?copy_addr) (unat ?here) =
				           (unat (mode_t_C.mode_C bm_res),
				            enc_best_bytes (mode_t_C.mode_C bm_res)
				              (mode_t_C.arg_C bm_res),
				            cache_update ?c1 (unat ?copy_addr))"
				          by (rule best_mode'_encode_address_exact[
				            OF abs_res wf_res bm_res])
				        have pure_len:
				          "length (case encode_address ?c1 (unat ?copy_addr)
				              (unat ?here) of (_, bs, _) \<Rightarrow> bs) \<le> 1"
				          using encode_address_cache_update_plus6_len_le1[
				            OF cache_wf, of "unat (match_t_C.pos_C m)"
				              "unat ?here"] copy_addr_unat
				          by simp
				        show ?thesis
				          using exact_res pure_len by simp
				      qed
				      have an_res_le1_if:
				        "mode_t_C.mode_C bm_res < (6 :: 32 word) \<Longrightarrow>
				          unat an_res \<le> 1"
				      proof -
				        assume mode_lt: "mode_t_C.mode_C bm_res < (6 :: 32 word)"
				        have "unat an_res =
				          length (varint_encode
				            (unat (mode_t_C.arg_C bm_res)))"
				          using varint_size'_unat_eq_varint_size[OF an_res]
				          by simp
				        also have "... =
				          length (enc_best_bytes (mode_t_C.mode_C bm_res)
				            (mode_t_C.arg_C bm_res))"
				          using mode_lt by (simp add: enc_best_bytes_def)
				        finally show "unat an_res \<le> 1"
				          using addr_bytes_len_res by simp
				      qed
				      have inst_room_res:
				        "unat (sections_t_C.inst_pos_C ?sec_f) + 6
				          \<le> unat inst_cap"
				        using inst_slack inst_suc_unat pend_ge_nat
				        by (simp; linarith)
				      have addr_room_res:
				        "unat (sections_t_C.addr_pos_C ?sec_f) + 5
				          \<le> unat addr_cap"
				        using addr_slack addr_an_unat an_le5
				        by (simp; linarith)
				      have emit:
				        "emit_copy' ?sec_f inst inst_cap addr addr_cap
				           ?copy_addr ?here ?copy_len \<bullet> taaa
				         \<lbrace> \<lambda>r u. \<exists>sec' inst_inc addr_inc.
				            r = Result sec' \<and>
				            sections_result sec'
				              (sections_t_C.data_pos_C ?sec_f)
				              (sections_t_C.inst_pos_C ?sec_f + inst_inc)
				              (sections_t_C.addr_pos_C ?sec_f + addr_inc)
				              ENC_OK \<and>
				            unat inst_inc \<le> 6 \<and>
				            unat addr_inc \<le> 5 \<and>
				            unat addr_inc \<le>
				              (if mode_t_C.mode_C bm_res < (6 :: 32 word)
				               then unat an_res else 1) \<and>
				            heap_bytes u src (unat src_len) =
				              heap_bytes taaa src (unat src_len) \<and>
				            heap_bytes u tgt (unat tgt_len) =
				              heap_bytes taaa tgt (unat tgt_len) \<and>
				            enc_cache_abs u
				              (cache_update ?c1 (unat ?copy_addr)) \<and>
				            enc_cache_wf
				              (cache_update ?c1 (unat ?copy_addr)) \<and>
					            heap_typing u = heap_typing taaa \<rbrace>"
					        apply (rule emit_copy'_success_heap_bytes2_cache_frame_bounded[
					          where c = ?c1 and m = bm_res and an = an_res
					            and sn = sn_res])
					        subgoal by (rule abs_res)
					        subgoal by (rule wf_res)
					        subgoal by (rule bm_res)
					        subgoal by (rule mode_res_le8)
					        subgoal by (rule an_res)
					        subgoal by (rule sn_res)
					        subgoal using sec_ok by simp
					        subgoal using prems inst_valid by (simp add: buf_valid_def)
					        subgoal using prems addr_valid by (simp add: buf_valid_def)
					        subgoal by (rule inst_dist)
					        subgoal by (rule addr_dist)
					        subgoal by (rule src_inst_disj)
					        subgoal by (rule tgt_inst_disj)
					        subgoal by (rule src_addr_disj)
					        subgoal by (rule tgt_addr_disj)
					        subgoal by (rule inst_room_res)
					        subgoal by (rule addr_room_res)
					        done
					      show ?thesis
					        apply simp
					        apply (rule runs_to_weaken[OF emit])
				        subgoal premises emit_post for r u
				        proof -
				          obtain sec' inst_inc addr_inc where r_def:
				            "r = Result sec'"
				            and sec_res:
				            "sections_result sec'
				              (sections_t_C.data_pos_C ?sec_f)
				              (sections_t_C.inst_pos_C ?sec_f + inst_inc)
				              (sections_t_C.addr_pos_C ?sec_f + addr_inc)
				              ENC_OK"
				            and inst_inc_le: "unat inst_inc \<le> 6"
				            and addr_inc_payload:
				            "unat addr_inc \<le>
				              (if mode_t_C.mode_C bm_res < (6 :: 32 word)
				               then unat an_res else 1)"
				            and src_heap_u:
				            "heap_bytes u src (unat src_len) =
				              heap_bytes taaa src (unat src_len)"
				            and tgt_heap_u:
				            "heap_bytes u tgt (unat tgt_len) =
				              heap_bytes taaa tgt (unat tgt_len)"
				            and cache_abs_u:
				            "enc_cache_abs u
				              (cache_update ?c1 (unat ?copy_addr))"
					            and cache_wf_u:
					            "enc_cache_wf
					              (cache_update ?c1 (unat ?copy_addr))"
					            using emit_post by clarsimp
				          have addr_inc_le1: "unat addr_inc \<le> 1"
				            using addr_inc_payload an_res_le1_if
				            by (cases "mode_t_C.mode_C bm_res <
				                (6 :: 32 word)") simp_all
				          have data_final_unat:
				            "unat (sections_t_C.data_pos_C sec') =
				              unat (sections_t_C.data_pos_C sec) +
				              unat pend_len"
				            using sec_res data_pend_unat
				            by (simp add: sections_result_def)
				          have data_room_final:
				            "unat (sections_t_C.data_pos_C sec') +
				              (unat tgt_len -
				                unat (tp + match_t_C.len_C m)) + 64
				              \<le> unat data_cap"
				            using data_slack data_final_unat tp_len_unat
				              tp_len_le_nat
				            by linarith
				          have inst_final_nat_bound:
				            "Suc (unat (sections_t_C.inst_pos_C sec)) +
				              unat inst_inc +
				              (unat tgt_len -
				                unat (tp + match_t_C.len_C m)) + 64
				              \<le> unat inst_cap"
				            using inst_slack inst_inc_le pend_ge_nat
				              copy_gt6_nat tp_len_unat tp_len_le_nat
				            by linarith
				          have inst_final_no_overflow:
					            "unat (sections_t_C.inst_pos_C sec + 1) +
					              unat inst_inc < 2 ^ 32"
					            using inst_final_nat_bound inst_suc_unat
					              unat_lt2p[of inst_cap] by (simp; linarith)
				          have inst_final_unat:
				            "unat (sections_t_C.inst_pos_C sec + 1 +
				              inst_inc) =
				             Suc (unat (sections_t_C.inst_pos_C sec)) +
				              unat inst_inc"
				            using inst_final_no_overflow inst_suc_unat
				            by (simp add: unat_word_add_no_overflow)
				          have inst_pos_final:
				            "unat (sections_t_C.inst_pos_C sec') =
				             Suc (unat (sections_t_C.inst_pos_C sec)) +
				              unat inst_inc"
				            using sec_res inst_final_unat
				            by (simp add: sections_result_def)
				          have inst_room_final:
				            "unat (sections_t_C.inst_pos_C sec') +
				              (unat tgt_len -
				                unat (tp + match_t_C.len_C m)) + 64
				              \<le> unat inst_cap"
				            using inst_final_nat_bound inst_pos_final by simp
				          have addr_final_nat_bound:
				            "unat (sections_t_C.addr_pos_C sec) +
				              unat an + unat addr_inc +
				              (unat tgt_len -
				                unat (tp + match_t_C.len_C m)) + 64
				              \<le> unat addr_cap"
				            using addr_slack an_le5 addr_inc_le1 pend_ge_nat
				              copy_gt6_nat tp_len_unat tp_len_le_nat
				            by linarith
				          have addr_final_no_overflow:
					            "unat (sections_t_C.addr_pos_C sec + an) +
					              unat addr_inc < 2 ^ 32"
					            using addr_final_nat_bound addr_an_unat
					              unat_lt2p[of addr_cap] by (simp; linarith)
				          have addr_final_unat:
				            "unat (sections_t_C.addr_pos_C sec + an +
				              addr_inc) =
				             unat (sections_t_C.addr_pos_C sec) +
				              unat an + unat addr_inc"
				            using addr_final_no_overflow addr_an_unat
				            by (simp add: unat_word_add_no_overflow)
				          have addr_pos_final:
				            "unat (sections_t_C.addr_pos_C sec') =
				             unat (sections_t_C.addr_pos_C sec) +
				              unat an + unat addr_inc"
				            using sec_res addr_final_unat
				            by (simp add: sections_result_def)
				          have addr_room_final:
				            "unat (sections_t_C.addr_pos_C sec') +
				              (unat tgt_len -
				                unat (tp + match_t_C.len_C m)) + 64
				              \<le> unat addr_cap"
				            using addr_final_nat_bound addr_pos_final by simp
				          have loop_ex:
				            "\<exists>spec_st''. encode_window_loop_rel u
				              src src_len tgt tgt_len data data_cap
				              inst inst_cap addr addr_cap pending pending_cap
				              sec' (tp + match_t_C.len_C m) 0
				              src_bytes tgt_bytes spec_st''"
				            apply (rule encode_window_loop_rel_zero_pending_witness[
				              where c = "cache_update ?c1 (unat ?copy_addr)"])
				            using src_heap_u tgt_heap_u prems src_heap0 tgt_heap0
				              src_len_eq tgt_len_eq sec_res tp_len_le_nat
				              data_room_final inst_room_final addr_room_final
				              cache_abs_u cache_wf_u data_final_unat
				              inst_pos_final addr_pos_final
				            by (simp_all add: sections_result_def)
				          then obtain spec_st'' where loop_rel_u:
				            "encode_window_loop_rel u
				              src src_len tgt tgt_len data data_cap
				              inst inst_cap addr addr_cap pending pending_cap
				              sec' (tp + match_t_C.len_C m) 0
				              src_bytes tgt_bytes spec_st''"
				            by blast
				          have enc_tp_less:
				            "enc_tp spec_st < enc_tp spec_st''"
				            using rel loop_rel_u tp_len_progress
				            by (simp add: encode_window_loop_rel_def)
				          have measure_rel:
				            "(((0, sec', tp + match_t_C.len_C m), u),
				              ((pend_len, sec, tp), s)) \<in>
				              measure
				                (\<lambda>((_ :: 32 word, _ :: sections_t_C,
				                    tp :: 32 word), _).
				                   unat tgt_len - unat tp)"
				            using measure_progress by simp
					          show ?thesis
					            using r_def sec_res loop_rel_u enc_tp_less measure_rel
				            apply (simp add: sections_result_def)
					            apply runs_to_vcg
					            by blast
					        qed
			    done
					  qed
			    done
					  qed
					  have high_branch:
				    "\<not> unat (mode_t_C.mode_C bm) \<le> 5 \<Longrightarrow>
				      encode_window_c_match_branch src_len
				        data data_cap inst inst_cap addr addr_cap
				        pending pend_len sec tp m \<bullet> s \<lbrace> ?Post \<rbrace>"
				  proof -
			    assume False: "\<not> unat (mode_t_C.mode_C bm) \<le> 5"
		    let ?c1 =
		      "cache_update (enc_cache spec_st) (unat (match_t_C.pos_C m))"
		    have mode_gt_word: "(5 :: 32 word) < mode_t_C.mode_C bm"
		      by (rule mode_gt5_of_not_nat_le5[OF False])
		    have copy_eq: "match_t_C.len_C m = (4 :: 32 word)"
		      using spec_mode_gt5_copy_ne4_false_nat[OF False] by blast
		    have tp4_eq:
		      "tp + (4 :: 32 word) = tp + match_t_C.len_C m"
		      using copy_eq by simp
		    have data_room_fused:
		      "\<And>sec'. sections_result sec'
		          (sections_t_C.data_pos_C sec + pend_len)
		          (sections_t_C.inst_pos_C sec + 1)
		          (sections_t_C.addr_pos_C sec + 1) ENC_OK \<Longrightarrow>
		        unat (sections_t_C.data_pos_C sec') +
		          (unat tgt_len - unat (tp + (4 :: 32 word))) + 64
		        \<le> unat data_cap"
		      using data_slack data_pend_unat tp_len_unat tp_len_le_nat
		        tp4_eq
		      by (simp add: sections_result_def; linarith)
		    have inst_room_fused:
		      "\<And>sec'. sections_result sec'
		          (sections_t_C.data_pos_C sec + pend_len)
		          (sections_t_C.inst_pos_C sec + 1)
		          (sections_t_C.addr_pos_C sec + 1) ENC_OK \<Longrightarrow>
		        unat (sections_t_C.inst_pos_C sec') +
		          (unat tgt_len - unat (tp + (4 :: 32 word))) + 64
		        \<le> unat inst_cap"
		      using inst_slack inst_suc_unat pend_ge_nat tp_len_unat
		        tp_len_le_nat copy_ge_nat tp4_eq
		      by (simp add: sections_result_def; linarith)
		    have addr_room_fused:
		      "\<And>sec'. sections_result sec'
		          (sections_t_C.data_pos_C sec + pend_len)
		          (sections_t_C.inst_pos_C sec + 1)
		          (sections_t_C.addr_pos_C sec + 1) ENC_OK \<Longrightarrow>
		        unat (sections_t_C.addr_pos_C sec') +
		          (unat tgt_len - unat (tp + (4 :: 32 word))) + 64
		        \<le> unat addr_cap"
		      using addr_slack addr_suc_unat pend_ge_nat tp_len_unat
		        tp_len_le_nat copy_ge_nat tp4_eq
		      by (simp add: sections_result_def; linarith)
		    have loop_progress:
		      "\<And>st sec'. \<lbrakk>
		        sections_result sec'
		          (sections_t_C.data_pos_C sec + pend_len)
		          (sections_t_C.inst_pos_C sec + 1)
		          (sections_t_C.addr_pos_C sec + 1) ENC_OK;
		        heap_bytes st src (unat src_len) = src_bytes;
		        heap_bytes st tgt (unat tgt_len) = tgt_bytes;
		        enc_cache_abs st ?c1; enc_cache_wf ?c1\<rbrakk> \<Longrightarrow>
		        \<exists>spec_st''. encode_window_loop_rel st
		          src src_len tgt tgt_len data data_cap
		          inst inst_cap addr addr_cap pending pending_cap
		          sec' (tp + (4 :: 32 word)) 0
		          src_bytes tgt_bytes spec_st'' \<and>
		          enc_tp spec_st < enc_tp spec_st'' \<and>
		          (((0, sec', tp + (4 :: 32 word)), st),
		            ((pend_len, sec, tp), s)) \<in>
		            measure
		              (\<lambda>((_ :: 32 word, _ :: sections_t_C,
		                  tp :: 32 word), _).
		                 unat tgt_len - unat tp)"
		    proof -
		      fix st sec'
		      assume sec_res:
		          "sections_result sec'
		            (sections_t_C.data_pos_C sec + pend_len)
		            (sections_t_C.inst_pos_C sec + 1)
		            (sections_t_C.addr_pos_C sec + 1) ENC_OK"
		        and st_src: "heap_bytes st src (unat src_len) = src_bytes"
		        and st_tgt: "heap_bytes st tgt (unat tgt_len) = tgt_bytes"
		        and st_abs: "enc_cache_abs st ?c1"
		        and st_wf: "enc_cache_wf ?c1"
		      have loop_ex:
		        "\<exists>spec_st''. encode_window_loop_rel st
		          src src_len tgt tgt_len data data_cap
		          inst inst_cap addr addr_cap pending pending_cap
		          sec' (tp + (4 :: 32 word)) 0
		          src_bytes tgt_bytes spec_st''"
		        apply (rule encode_window_loop_rel_zero_pending_witness[
		          where c = ?c1])
		        subgoal by (rule st_src)
		        subgoal by (rule st_tgt)
		        subgoal by (rule src_len_eq)
		        subgoal by (rule tgt_len_eq)
		        subgoal using sec_res by (simp add: sections_result_def)
		        subgoal using tp_len_le_nat tp4_eq by simp
		        subgoal using data_room_fused[OF sec_res] by (simp; linarith)
		        subgoal using inst_room_fused[OF sec_res] by (simp; linarith)
		        subgoal using addr_room_fused[OF sec_res] by (simp; linarith)
		        subgoal using data_room_fused[OF sec_res] by simp
		        subgoal using inst_room_fused[OF sec_res] by simp
		        subgoal using addr_room_fused[OF sec_res] by simp
		        subgoal by (rule st_abs)
		        subgoal by (rule st_wf)
		        done
		      then obtain spec_st'' where loop_rel_st:
		        "encode_window_loop_rel st
		          src src_len tgt tgt_len data data_cap
		          inst inst_cap addr addr_cap pending pending_cap
		          sec' (tp + (4 :: 32 word)) 0
		          src_bytes tgt_bytes spec_st''"
		        by blast
		      have enc_tp_less:
		        "enc_tp spec_st < enc_tp spec_st''"
		        using rel loop_rel_st tp_len_progress tp4_eq
		        by (simp add: encode_window_loop_rel_def)
		      have measure_rel:
		        "(((0, sec', tp + (4 :: 32 word)), st),
		          ((pend_len, sec, tp), s)) \<in>
		          measure
		            (\<lambda>((_ :: 32 word, _ :: sections_t_C,
		                tp :: 32 word), _).
		               unat tgt_len - unat tp)"
		        using measure_progress tp4_eq by simp
		      show "\<exists>spec_st''. encode_window_loop_rel st
		          src src_len tgt tgt_len data data_cap
		          inst inst_cap addr addr_cap pending pending_cap
		          sec' (tp + (4 :: 32 word)) 0
		          src_bytes tgt_bytes spec_st'' \<and>
		          enc_tp spec_st < enc_tp spec_st'' \<and>
		          (((0, sec', tp + (4 :: 32 word)), st),
		            ((pend_len, sec, tp), s)) \<in>
		            measure
		              (\<lambda>((_ :: 32 word, _ :: sections_t_C,
		                  tp :: 32 word), _).
		                 unat tgt_len - unat tp)"
		        using loop_rel_st enc_tp_less measure_rel by blast
		    qed
		    have try_gt5_frame:
		      "try_emit_add_copy' sec data data_cap inst inst_cap
		          addr addr_cap pending pend_len
		          (match_t_C.pos_C m) (src_len + tp) (match_t_C.len_C m) \<bullet> s
		       \<lbrace> \<lambda>r t. \<exists>f.
		            r = Result f \<and>
		            fused_t_C.fused_C f = match_t_C.len_C m \<and>
		            sections_result (fused_t_C.s_C f)
		              (sections_t_C.data_pos_C sec + pend_len)
		              (sections_t_C.inst_pos_C sec + 1)
		              (sections_t_C.addr_pos_C sec + 1) ENC_OK \<and>
		            heap_bytes t src (unat src_len) = src_bytes \<and>
		            heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
		            enc_cache_abs t ?c1 \<and>
		            enc_cache_wf ?c1 \<and>
		            heap_typing t = heap_typing s \<rbrace>"
			    proof -
			      have near_ptr_lt:
			        "near_ptr_'' s < (4 :: 32 word)"
			        by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
			      have emitted0:
			        "emitted_sections s data inst addr sec
			          (heap_bytes s data (unat (sections_t_C.data_pos_C sec)))
			          (heap_bytes s inst (unat (sections_t_C.inst_pos_C sec)))
			          (heap_bytes s addr (unat (sections_t_C.addr_pos_C sec)))"
			        by (simp add: emitted_sections_def)
			      have sections_run:
			        "try_emit_add_copy' sec data data_cap inst inst_cap
			            addr addr_cap pending pend_len
			            (match_t_C.pos_C m) (src_len + tp) (match_t_C.len_C m) \<bullet> s
			         \<lbrace> \<lambda>r t.
			              (\<exists>f.
			                r = Result f \<and>
			                fused_t_C.fused_C f = match_t_C.len_C m \<and>
			                sections_result (fused_t_C.s_C f)
				                  (sections_t_C.data_pos_C sec + pend_len)
				                  (sections_t_C.inst_pos_C sec + 1)
				                  (sections_t_C.addr_pos_C sec + 1) ENC_OK) \<and>
				              heap_typing t = heap_typing s \<rbrace>"
				        apply (rule runs_to_weaken[
				          OF try_emit_add_copy'_mode_gt5_success_emitted_sections[
				            OF emitted0 bm pend_ge pend_le copy_eq mode_gt_word
				               mode_le8 sec_ok near_ptr_lt inst_byte_room
				               inst_byte_ptr inst_suc_dist inst_byte_data_disj
				               inst_byte_addr_disj inst_byte_pending_disj data_fits
				               data_write_valid pending_write_valid data_pending_disj
				               data_inj data_prefix_disj data_pend_no_overflow
				               data_inst_disj data_addr_disj addr_byte_room
				               addr_byte_ptr addr_suc_dist addr_byte_data_disj
				               addr_byte_inst_disj]])
				        by auto
			      have op_nz:
			        "(0xD2 + (mode_t_C.mode_C bm * 4 + pend_len) ::
			          32 word) \<noteq> 0"
			        by (rule op_d2_nz_gt5_nat[OF False])
				      have mode_not_lt6:
				        "\<not> mode_t_C.mode_C bm < (6 :: 32 word)"
				        using mode_gt_word by (simp add: word_less_nat_alt)
				      note add_copy_opcode'_mode_gt5[runs_to_vcg]
				      have heap_cache_run:
				        "try_emit_add_copy' sec data data_cap inst inst_cap
				            addr addr_cap pending pend_len
				            (match_t_C.pos_C m) (src_len + tp) (match_t_C.len_C m) \<bullet> s
				         \<lbrace> \<lambda>r t. \<exists>f.
				              r = Result f \<and>
				              fused_t_C.fused_C f = match_t_C.len_C m \<and>
				              heap_bytes t src (unat src_len) =
				                heap_bytes s src (unat src_len) \<and>
				              heap_bytes t tgt (unat tgt_len) =
				                heap_bytes s tgt (unat tgt_len) \<and>
					              enc_cache_abs t ?c1 \<and>
					              enc_cache_wf ?c1 \<and>
					              heap_typing t = heap_typing s \<rbrace>"
					        apply (rule runs_to_weaken[
					          OF try_emit_add_copy'_mode_gt5_success_heap_bytes2_cache_frame[
					            OF abs cache_wf bm pend_ge pend_le copy_eq
					               mode_gt_word mode_le8 sec_ok inst_byte_room
					               inst_byte_ptr src_inst_byte_disj
					               tgt_inst_byte_disj data_fits data_write_valid
					               pending_write_valid src_data_write_disj
					               tgt_data_write_disj addr_byte_room addr_byte_ptr
					               addr_suc_dist src_addr_byte_disj
					               tgt_addr_byte_disj]])
					        by auto
				      have combined:
				        "try_emit_add_copy' sec data data_cap inst inst_cap
			            addr addr_cap pending pend_len
			            (match_t_C.pos_C m) (src_len + tp) (match_t_C.len_C m) \<bullet> s
			         \<lbrace> \<lambda>r t.
			              ((\<exists>f.
			                r = Result f \<and>
			                fused_t_C.fused_C f = match_t_C.len_C m \<and>
			                sections_result (fused_t_C.s_C f)
			                  (sections_t_C.data_pos_C sec + pend_len)
			                  (sections_t_C.inst_pos_C sec + 1)
			                  (sections_t_C.addr_pos_C sec + 1) ENC_OK) \<and>
			               heap_typing t = heap_typing s) \<and>
			              (\<exists>f.
			                r = Result f \<and>
			                fused_t_C.fused_C f = match_t_C.len_C m \<and>
			                heap_bytes t src (unat src_len) =
			                  heap_bytes s src (unat src_len) \<and>
				                heap_bytes t tgt (unat tgt_len) =
				                  heap_bytes s tgt (unat tgt_len) \<and>
				                enc_cache_abs t ?c1 \<and>
				                enc_cache_wf ?c1 \<and>
				                heap_typing t = heap_typing s) \<rbrace>"
				        using sections_run heap_cache_run by (simp add: runs_to_conj)
					      show ?thesis
					        apply (rule runs_to_weaken[OF combined])
					        using src_heap0 tgt_heap0 by auto
				    qed
						    let ?Q = ?Post
					    let ?cont =
					      "\<lambda>f. do {
					          unless (sections_t_C.err_C (fused_t_C.s_C f) = 0)
					            (throw (fused_t_C.s_C f));
					          condition (\<lambda>s. fused_t_C.fused_C f \<noteq> 0)
					            (do {
					              (sec_run, tp_run) \<leftarrow>
					                condition
					                  (\<lambda>s. fused_t_C.fused_C f < match_t_C.len_C m)
					                  (do {
					                    sec_run \<leftarrow> liftE
					                      (emit_copy' (fused_t_C.s_C f) inst
					                        inst_cap addr addr_cap
					                        (match_t_C.pos_C m +
					                          fused_t_C.fused_C f)
					                        (src_len +
					                          (tp + fused_t_C.fused_C f))
					                        (match_t_C.len_C m -
					                          fused_t_C.fused_C f));
					                    unless (sections_t_C.err_C sec_run = 0)
					                      (throw sec_run);
					                    return (sec_run, tp + match_t_C.len_C m)
					                  })
					                  (return (fused_t_C.s_C f,
					                    tp + fused_t_C.fused_C f));
					              return (0, sec_run, tp_run)
					            })
					            (do {
					              (pend_len_run, sec_run) \<leftarrow>
					                condition (\<lambda>s. 0 < pend_len)
					                  (do {
					                    sec_run \<leftarrow> liftE
					                      (flush_pending' sec data data_cap inst
					                        inst_cap pending pend_len);
					                    unless (sections_t_C.err_C sec_run = 0)
					                      (throw sec_run);
					                    return (0, sec_run)
					                  })
					                  (return (pend_len, sec));
					              sec_run \<leftarrow> liftE
					                (emit_copy' sec_run inst inst_cap addr addr_cap
					                  (match_t_C.pos_C m) (src_len + tp)
					                  (match_t_C.len_C m));
					              unless (sections_t_C.err_C sec_run = 0)
					                (throw sec_run);
					              return (pend_len_run, sec_run,
					                tp + match_t_C.len_C m)
					            })
					        }"
					    have fused_cont:
					      "\<And>f st. \<lbrakk>
					        fused_t_C.fused_C f = match_t_C.len_C m;
					        sections_result (fused_t_C.s_C f)
					          (sections_t_C.data_pos_C sec + pend_len)
				          (sections_t_C.inst_pos_C sec + 1)
				          (sections_t_C.addr_pos_C sec + 1) ENC_OK;
					        heap_bytes st src (unat src_len) = src_bytes;
					        heap_bytes st tgt (unat tgt_len) = tgt_bytes;
					        enc_cache_abs st ?c1;
					        enc_cache_wf ?c1\<rbrakk> \<Longrightarrow>
					        ?cont f \<bullet> st \<lbrace> ?Q \<rbrace>"
					    proof -
					      fix f st
					      assume fused_len:
					          "fused_t_C.fused_C f = match_t_C.len_C m"
				        and sec_res:
				          "sections_result (fused_t_C.s_C f)
				            (sections_t_C.data_pos_C sec + pend_len)
				            (sections_t_C.inst_pos_C sec + 1)
				            (sections_t_C.addr_pos_C sec + 1) ENC_OK"
				        and st_src:
				          "heap_bytes st src (unat src_len) = src_bytes"
				        and st_tgt:
				          "heap_bytes st tgt (unat tgt_len) = tgt_bytes"
				        and st_abs: "enc_cache_abs st ?c1"
				        and st_wf: "enc_cache_wf ?c1"
					      have loop_after:
					        "\<exists>spec_st''. encode_window_loop_rel st
					          src src_len tgt tgt_len data data_cap inst inst_cap
					          addr addr_cap pending pending_cap
					          (fused_t_C.s_C f) (tp + (4 :: 32 word)) 0
				          src_bytes tgt_bytes spec_st'' \<and>
				          enc_tp spec_st < enc_tp spec_st'' \<and>
				          (((0, fused_t_C.s_C f, tp + (4 :: 32 word)), st),
				            ((pend_len, sec, tp), s)) \<in>
				            measure
					              (\<lambda>((_ :: 32 word, _ :: sections_t_C,
					                  tp :: 32 word), _).
					                 unat tgt_len - unat tp)"
					        using loop_progress[
					          OF sec_res st_src st_tgt st_abs st_wf] by blast
					      show "?cont f \<bullet> st \<lbrace> ?Q \<rbrace>"
					        using fused_len copy_eq sec_res loop_after
					        by (auto simp: sections_result_def runs_to_bind_iff
					          runs_to_condition_iff)
					    qed
				    have try_gt5_lifted:
				      "liftE
				        (try_emit_add_copy' sec data data_cap inst inst_cap
				          addr addr_cap pending pend_len
				          (match_t_C.pos_C m) (src_len + tp)
				          (match_t_C.len_C m)) \<bullet> s
				       \<lbrace> \<lambda>r t. \<exists>f.
				            r = Result f \<and>
				            fused_t_C.fused_C f = match_t_C.len_C m \<and>
				            sections_result (fused_t_C.s_C f)
				              (sections_t_C.data_pos_C sec + pend_len)
				              (sections_t_C.inst_pos_C sec + 1)
				              (sections_t_C.addr_pos_C sec + 1) ENC_OK \<and>
				            heap_bytes t src (unat src_len) = src_bytes \<and>
				            heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
				            enc_cache_abs t ?c1 \<and>
				            enc_cache_wf ?c1 \<and>
				            heap_typing t = heap_typing s \<rbrace>"
					      apply (rule runs_to_liftE)
					      apply (rule runs_to_weaken[OF try_gt5_frame])
					      by auto
					    have try_gt5_for_bind:
					      "liftE
					        (try_emit_add_copy' sec data data_cap inst inst_cap
					          addr addr_cap pending pend_len
					          (match_t_C.pos_C m) (src_len + tp)
					          (match_t_C.len_C m)) \<bullet> s
					       \<lbrace> \<lambda>r t.
					            (\<forall>v. r = Result v \<longrightarrow>
					              ?cont v \<bullet> t \<lbrace> ?Q \<rbrace>) \<and>
					            (\<forall>e. r = Exception e \<longrightarrow>
					              e \<noteq> default \<longrightarrow> ?Q (Exception e) t) \<rbrace>"
					    proof (rule runs_to_weaken[OF try_gt5_lifted])
					      fix r t
					      assume "\<exists>f.
					            r = Result f \<and>
					            fused_t_C.fused_C f = match_t_C.len_C m \<and>
					            sections_result (fused_t_C.s_C f)
					              (sections_t_C.data_pos_C sec + pend_len)
					              (sections_t_C.inst_pos_C sec + 1)
					              (sections_t_C.addr_pos_C sec + 1) ENC_OK \<and>
					            heap_bytes t src (unat src_len) = src_bytes \<and>
					            heap_bytes t tgt (unat tgt_len) = tgt_bytes \<and>
					            enc_cache_abs t ?c1 \<and>
					            enc_cache_wf ?c1 \<and>
					            heap_typing t = heap_typing s"
					      then obtain f where r_def: "r = Result f"
					        and fused_len:
					          "fused_t_C.fused_C f = match_t_C.len_C m"
					        and sec_res:
					          "sections_result (fused_t_C.s_C f)
					            (sections_t_C.data_pos_C sec + pend_len)
					            (sections_t_C.inst_pos_C sec + 1)
					            (sections_t_C.addr_pos_C sec + 1) ENC_OK"
					        and st_src:
					          "heap_bytes t src (unat src_len) = src_bytes"
					        and st_tgt:
					          "heap_bytes t tgt (unat tgt_len) = tgt_bytes"
					        and st_abs: "enc_cache_abs t ?c1"
					        and st_wf: "enc_cache_wf ?c1"
					        by blast
					      show "(\<forall>v. r = Result v \<longrightarrow>
					              ?cont v \<bullet> t \<lbrace> ?Q \<rbrace>) \<and>
					            (\<forall>e. r = Exception e \<longrightarrow>
					              e \<noteq> default \<longrightarrow> ?Q (Exception e) t)"
					      proof (intro conjI allI impI)
					        fix v
					        assume rv: "r = Result v"
					        have v_eq: "v = f"
					          using r_def rv by simp
					        have cont_f: "?cont f \<bullet> t \<lbrace> ?Q \<rbrace>"
					          by (rule fused_cont[
					            OF fused_len sec_res st_src st_tgt st_abs st_wf])
					        have cont_eq: "?cont v = ?cont f"
					          using v_eq by simp
					        show "?cont v \<bullet> t \<lbrace> ?Q \<rbrace>"
					          using cont_eq cont_f by simp
					      next
					        fix e
					        assume "r = Exception e"
					          and "e \<noteq> default"
					        then show "?Q (Exception e) t"
					          using r_def by simp
					      qed
					    qed
						    have branch_unfold:
						      "encode_window_c_match_branch src_len
						        data data_cap inst inst_cap addr addr_cap
						        pending pend_len sec tp m =
						       bind (liftE
						        (try_emit_add_copy' sec data data_cap inst inst_cap
						          addr addr_cap pending pend_len
						          (match_t_C.pos_C m) (src_len + tp)
						          (match_t_C.len_C m))) ?cont"
						      by (simp add: encode_window_c_match_branch_def)
						    have branch_run:
						      "bind (liftE
						        (try_emit_add_copy' sec data data_cap inst inst_cap
						          addr addr_cap pending pend_len
						          (match_t_C.pos_C m) (src_len + tp)
						          (match_t_C.len_C m))) ?cont \<bullet> s \<lbrace> ?Q \<rbrace>"
						      by (rule runs_to_bind[OF try_gt5_for_bind])
							    have branch_lhs_run:
							      "encode_window_c_match_branch src_len
							        data data_cap inst inst_cap addr addr_cap
							        pending pend_len sec tp m \<bullet> s \<lbrace> ?Q \<rbrace>"
						      apply (subst branch_unfold)
							      apply (rule branch_run)
							      done
							    show ?thesis
							      by (rule branch_lhs_run)
				  qed
				  show ?thesis
				  proof (cases "unat (mode_t_C.mode_C bm) \<le> 5")
				    case True
				    show ?thesis by (rule low_branch[OF True])
				  next
				    case False
				    show ?thesis by (rule high_branch[OF False])
				  qed
	qed

lemma encode_window_flush_then_copy_step_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and tp_lt: "tp < tgt_len"
      and match:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
      and match_len: "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
      and fused_none:
    "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st =
      None"
  shows "encode_window_c_match_branch src_len
            data data_cap inst inst_cap addr addr_cap pending pend_len
            sec tp m \<bullet> s
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
  sorry

lemma encode_window_match_step_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
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
  have find_run:
    "gets_the (find_best_match' src src_len tgt tgt_len tp head_arr next_arr)
      \<bullet> s \<lbrace> \<lambda>r t. t = s \<and> r = Result m \<rbrace>"
    unfolding gets_the_def
    apply runs_to_vcg
    using match by simp
  have match_not_short:
    "\<not> match_t_C.len_C m < (of_nat min_match :: 32 word)"
    using match_len
    by simp
  show ?thesis
  proof (cases "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st")
    case None
    show ?thesis
      unfolding encode_window_c_loop_body_def
      apply simp
      apply (rule runs_to_bind)
       apply (rule runs_to_weaken[OF find_run])
      apply clarsimp
      using match_not_short
      apply (simp add: min_match_def)
      apply (fold encode_window_c_match_branch_def)
      apply (rule runs_to_weaken[
	        OF encode_window_flush_then_copy_step_topdown[
	          OF rel buffers match_rel src_tgt_bound tp_lt match match_len None]])
      apply clarsimp
      done
  next
    case (Some fused)
    show ?thesis
      unfolding encode_window_c_loop_body_def
      apply simp
      apply (rule runs_to_bind)
       apply (rule runs_to_weaken[OF find_run])
      apply clarsimp
      using match_not_short
      apply (simp add: min_match_def)
      apply (fold encode_window_c_match_branch_def)
      apply (rule runs_to_weaken[
	        OF encode_window_try_fused_copy_step_topdown[
	          OF rel buffers match_rel src_tgt_bound tp_lt match match_len Some]])
      apply clarsimp
      done
  qed
qed

lemma encode_window_loop_body_topdown:
  assumes rel:
    "encode_window_loop_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and pend_lt: "pend_len < pending_cap"
      and tp_lt: "tp < tgt_len"
      and match_result:
    "\<exists>m. find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
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
    by (rule encode_window_pending_byte_step_topdown[
        OF rel buffers pend_lt tp_lt])
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
    by (rule encode_window_match_step_topdown[
        OF rel buffers match_rel src_tgt_bound tp_lt])
  show ?thesis
  proof -
    obtain m where m_result:
      "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
        Some m"
      using match_result by blast
    show ?thesis
    proof (cases "match_t_C.len_C m < (of_nat min_match :: 32 word)")
      case True
      show ?thesis
      proof (rule runs_to_weaken[OF pending_case[OF True m_result]])
        fix r t
        assume post:
          "\<exists>sec' tp' pend_len' spec_st'.
            r = Result (pend_len', sec', tp') \<and>
            spec_st' = buffer_pending_byte_spec (tgt_bytes ! unat tp)
              spec_st \<and>
            encode_window_loop_rel t src src_len tgt tgt_len
              data data_cap inst inst_cap addr addr_cap pending pending_cap
              sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
            (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
              measure
                (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                   unat tgt_len - unat tp)"
        then obtain sec' tp' pend_len' spec_st' where
          r_eq: "r = Result (pend_len', sec', tp')"
          and spec_eq:
            "spec_st' = buffer_pending_byte_spec (tgt_bytes ! unat tp)
              spec_st"
          and rel':
            "encode_window_loop_rel t src src_len tgt tgt_len
              data data_cap inst inst_cap addr addr_cap pending pending_cap
              sec' tp' pend_len' src_bytes tgt_bytes spec_st'"
          and meas:
            "(((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
              measure
                (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                   unat tgt_len - unat tp)"
          by blast
        have progress: "enc_tp spec_st < enc_tp spec_st'"
          using spec_eq by (simp add: buffer_pending_byte_spec_def)
        show "\<exists>sec' tp' pend_len' spec_st'.
          r = Result (pend_len', sec', tp') \<and>
          encode_window_loop_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
          enc_tp spec_st < enc_tp spec_st' \<and>
          (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp)"
          using r_eq rel' progress meas by blast
      qed
    next
      case False
      have match_len:
        "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
        using False by simp
      show ?thesis
        by (rule match_case[OF m_result match_len])
    qed
  qed
qed

lemma encode_window_match_rel_short_spec:
  assumes rel:
    "encode_window_loop_budget_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and tp_lt: "tp < tgt_len"
      and match:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
      and short: "match_t_C.len_C m < (of_nat min_match :: 32 word)"
  shows "em_len (find_best_match_spec src_bytes tgt_bytes (enc_tp spec_st)
          (build_index_spec src_bytes)) < min_match"
proof -
  let ?best =
    "find_best_match_spec src_bytes tgt_bytes (unat tp)
      (build_index_spec src_bytes)"
  have tp_eq: "enc_tp spec_st = unat tp"
    using rel by (simp add: encode_window_loop_budget_rel_def)
  have tgt_len_eq: "length tgt_bytes = unat tgt_len"
    using rel by (simp add: encode_window_loop_budget_rel_def)
  have tp_le: "tp \<le> tgt_len"
    using tp_lt by simp
  have rel_match:
    "m = (let best =
             find_best_match_spec src_bytes tgt_bytes (unat tp)
               (build_index_spec src_bytes)
           in match_t_C (of_nat (em_pos best)) (of_nat (em_len best))) \<and>
     match_valid src_bytes tgt_bytes (unat tp)
       (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
    using match_rel tp_le match
    unfolding encode_window_match_rel_def by blast
  have m_eq:
    "m = match_t_C (of_nat (em_pos ?best)) (of_nat (em_len ?best))"
    using rel_match by (simp add: Let_def)
  show ?thesis
  proof (rule ccontr)
    assume not_short:
      "\<not> em_len (find_best_match_spec src_bytes tgt_bytes
        (enc_tp spec_st) (build_index_spec src_bytes)) < min_match"
    have best_not_short: "\<not> em_len ?best < min_match"
      using not_short tp_eq by simp
    then have min_le: "min_match \<le> em_len ?best"
      by simp
    have sound:
      "em_pos ?best + em_len ?best \<le> length src_bytes \<and>
       unat tp + em_len ?best \<le> length tgt_bytes \<and>
       (\<forall>k < em_len ?best.
          src_bytes ! (em_pos ?best + k) = tgt_bytes ! (unat tp + k))"
      by (rule find_best_match_spec_sound[OF refl min_le])
    have best_len32: "em_len ?best < 2 ^ 32"
    proof -
      have "em_len ?best \<le> unat tp + em_len ?best"
        by simp
      also have "... \<le> length tgt_bytes"
        using sound by simp
      also have "... = unat tgt_len"
        using tgt_len_eq by simp
      also have "... < 2 ^ 32"
        using unat_lt2p[of tgt_len] by simp
      finally show ?thesis .
    qed
    have c_len: "unat (match_t_C.len_C m) = em_len ?best"
      using m_eq best_len32 by (simp add: unat_of_nat)
    have c_short: "unat (match_t_C.len_C m) < min_match"
      using short by (simp add: min_match_def word_less_nat_alt)
    show False
      using min_le c_len c_short by linarith
  qed
qed

lemma encode_window_section_budget_buffer_pending_byte:
  assumes budget:
    "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap spec_st"
      and tp_lt: "enc_tp spec_st < length tgt_bytes"
      and short:
    "em_len (find_best_match_spec src_bytes tgt_bytes (enc_tp spec_st)
      (build_index_spec src_bytes)) < min_match"
  shows "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap
      (buffer_pending_byte_spec (tgt_bytes ! enc_tp spec_st) spec_st)"
proof -
  let ?idx = "build_index_spec src_bytes"
  let ?spec' =
    "buffer_pending_byte_spec (tgt_bytes ! enc_tp spec_st) spec_st"
  have reaches0:
    "encode_window_spec_reaches_final src_bytes tgt_bytes spec_st"
    using budget by (simp add: encode_window_section_budget_def)
  have step:
    "encode_window_full_loop (length tgt_bytes + 1 - enc_tp spec_st)
       src_bytes tgt_bytes ?idx spec_st =
     encode_window_full_loop (length tgt_bytes + 1 - enc_tp ?spec')
       src_bytes tgt_bytes ?idx ?spec'"
  proof -
    have fuel:
      "length tgt_bytes + 1 - enc_tp spec_st =
       Suc (length tgt_bytes - enc_tp spec_st)"
      using tp_lt by simp
    have fuel':
      "length tgt_bytes + 1 - enc_tp ?spec' =
       length tgt_bytes - enc_tp spec_st"
      using tp_lt by (simp add: buffer_pending_byte_spec_def)
    have step':
      "encode_window_full_step src_bytes tgt_bytes ?idx spec_st = ?spec'"
      using short by (simp add: encode_window_full_step_def Let_def)
    show ?thesis
    proof -
      have not_done: "\<not> enc_tp spec_st \<ge> length tgt_bytes"
        using tp_lt by simp
      have "encode_window_full_loop (length tgt_bytes + 1 - enc_tp spec_st)
              src_bytes tgt_bytes ?idx spec_st =
            encode_window_full_loop
              (Suc (length tgt_bytes - enc_tp spec_st))
              src_bytes tgt_bytes ?idx spec_st"
        by (simp only: fuel)
      also have "... =
            encode_window_full_loop (length tgt_bytes - enc_tp spec_st)
              src_bytes tgt_bytes ?idx
              (encode_window_full_step src_bytes tgt_bytes ?idx spec_st)"
        by (simp only: encode_window_full_loop_Suc not_done if_False)
      also have "... =
            encode_window_full_loop (length tgt_bytes - enc_tp spec_st)
              src_bytes tgt_bytes ?idx ?spec'"
        by (simp only: step')
      also have "... =
            encode_window_full_loop (length tgt_bytes + 1 - enc_tp ?spec')
              src_bytes tgt_bytes ?idx ?spec'"
        by (simp only: fuel')
      finally show ?thesis .
    qed
  qed
  have reaches':
    "encode_window_spec_reaches_final src_bytes tgt_bytes ?spec'"
    using reaches0 step
    by (simp add: encode_window_spec_reaches_final_def)
  have prefix':
    "encode_window_section_prefix_budget src_bytes tgt_bytes ?spec'"
    using budget
    by (simp add: encode_window_section_budget_def
        encode_window_section_prefix_budget_def
        buffer_pending_byte_spec_def)
  have caps:
    "encoder_final_section_caps_ok src_bytes tgt_bytes
      data_cap inst_cap addr_cap"
    using budget by (simp add: encode_window_section_budget_def)
  show ?thesis
    using reaches' prefix' caps
    by (simp add: encode_window_section_budget_def)
qed

lemma encode_window_pending_byte_step_topdown_budget:
  assumes rel:
    "encode_window_loop_budget_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and pend_lt: "pend_len < pending_cap"
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
              encode_window_loop_budget_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
	                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
	                     unat tgt_len - unat tp) \<rbrace>"
proof -
  let ?byte = "tgt_bytes ! unat tp"
  let ?written = "heap_w8 s (tgt +\<^sub>p uint tp)"
  let ?t =
    "heap_w8_update
      (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
             ?written)) s"
  let ?spec = "buffer_pending_byte_spec ?byte spec_st"
  have update_eq:
    "heap_w8_update
       (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
              h (tgt +\<^sub>p uint tp))) s = ?t"
    by simp
  have pend_nat_lt: "unat pend_len < unat pending_cap"
    using pend_lt by (simp add: word_less_nat_alt)
  have tp_nat_lt: "unat tp < unat tgt_len"
    using tp_lt by (simp add: word_less_nat_alt)
  have tp_suc_le: "Suc (unat tp) \<le> unat tgt_len"
    using tp_nat_lt by simp
  have pend_suc: "unat (pend_len + 1) = Suc (unat pend_len)"
    by (rule unat_suc_word_less[OF pend_lt])
  have tp_suc: "unat (tp + 1) = Suc (unat tp)"
    by (rule unat_suc_word_less[OF tp_lt])

  have pending_valid: "buf_valid s pending (unat pending_cap)"
    and tgt_valid: "buf_valid s tgt (unat tgt_len)"
    and pending_dist: "ptr_range_distinct pending (unat pending_cap)"
    and pending_src:
      "bufs_disjoint pending (unat pending_cap) src (unat src_len)"
    and pending_tgt:
      "bufs_disjoint pending (unat pending_cap) tgt (unat tgt_len)"
    and pending_data:
      "bufs_disjoint pending (unat pending_cap) data (unat data_cap)"
    and pending_inst:
      "bufs_disjoint pending (unat pending_cap) inst (unat inst_cap)"
    and pending_addr:
      "bufs_disjoint pending (unat pending_cap) addr (unat addr_cap)"
    using buffers
    by (simp_all add: encode_window_loop_buffers_ok_def)
  have pending_ptr:
    "ptr_valid (heap_typing s) (pending +\<^sub>p uint pend_len)"
    by (rule buf_valid_uintD[OF pending_valid pend_nat_lt])
  have tgt_ptr:
    "ptr_valid (heap_typing s) (tgt +\<^sub>p uint tp)"
    by (rule buf_valid_uintD[OF tgt_valid tp_nat_lt])

  have src_heap:
    "heap_bytes ?t src (unat src_len) = src_bytes"
  proof -
    have src_pending:
      "bufs_disjoint src (unat src_len) pending (unat pending_cap)"
      using pending_src by (simp add: bufs_disjoint_sym)
    have "heap_bytes ?t src (unat src_len) = heap_bytes s src (unat src_len)"
      by (rule heap_bytes_update_disjoint_prefix[
          OF src_pending pend_nat_lt order.refl])
    thus ?thesis
      using rel by (simp add: encode_window_loop_budget_rel_def)
  qed
  have tgt_heap:
    "heap_bytes ?t tgt (unat tgt_len) = tgt_bytes"
  proof -
    have tgt_pending:
      "bufs_disjoint tgt (unat tgt_len) pending (unat pending_cap)"
      using pending_tgt by (simp add: bufs_disjoint_sym)
    have "heap_bytes ?t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)"
      by (rule heap_bytes_update_disjoint_prefix[
          OF tgt_pending pend_nat_lt order.refl])
    thus ?thesis
      using rel by (simp add: encode_window_loop_budget_rel_def)
  qed
  have tgt_byte:
    "?written = ?byte"
  proof -
    have tgt_bytes_eq: "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
      using rel by (simp add: encode_window_loop_budget_rel_def)
    have nth_heap:
      "heap_bytes s tgt (unat tgt_len) ! unat tp =
       heap_w8 s (tgt +\<^sub>p int (unat tp))"
      by (rule heap_bytes_nth[OF tp_nat_lt])
    have byte_eq:
      "tgt_bytes ! unat tp =
       heap_w8 s (tgt +\<^sub>p int (unat tp))"
      using tgt_bytes_eq nth_heap by simp
    show ?thesis
      using byte_eq[symmetric] by (simp only: uint_nat)
  qed
  have pending_heap:
    "heap_bytes_word ?t pending 0 (pend_len + 1) =
       enc_pending ?spec"
  proof -
    have append:
      "heap_bytes_word ?t pending 0 (pend_len + 1) =
       heap_bytes_word s pending 0 pend_len @
       [?written]"
      by (rule heap_bytes_word_zero_update_append[OF pend_lt pending_dist])
    show ?thesis
      using append rel tgt_byte
      by (simp add: encode_window_loop_budget_rel_def
          buffer_pending_byte_spec_def)
  qed
  have data_heap:
    "heap_bytes ?t data (unat (sections_t_C.data_pos_C sec)) =
     heap_bytes s data (unat (sections_t_C.data_pos_C sec))"
  proof -
    have data_pending:
      "bufs_disjoint data (unat data_cap) pending (unat pending_cap)"
      using pending_data by (simp add: bufs_disjoint_sym)
    have data_le:
      "unat (sections_t_C.data_pos_C sec) \<le> unat data_cap"
      using rel by (simp add: encode_window_loop_budget_rel_def)
    show ?thesis
      by (rule heap_bytes_update_disjoint_prefix[
          OF data_pending pend_nat_lt data_le])
  qed
  have inst_heap:
    "heap_bytes ?t inst (unat (sections_t_C.inst_pos_C sec)) =
     heap_bytes s inst (unat (sections_t_C.inst_pos_C sec))"
  proof -
    have inst_pending:
      "bufs_disjoint inst (unat inst_cap) pending (unat pending_cap)"
      using pending_inst by (simp add: bufs_disjoint_sym)
    have inst_le:
      "unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap"
      using rel by (simp add: encode_window_loop_budget_rel_def)
    show ?thesis
      by (rule heap_bytes_update_disjoint_prefix[
          OF inst_pending pend_nat_lt inst_le])
  qed
  have addr_heap:
    "heap_bytes ?t addr (unat (sections_t_C.addr_pos_C sec)) =
     heap_bytes s addr (unat (sections_t_C.addr_pos_C sec))"
  proof -
    have addr_pending:
      "bufs_disjoint addr (unat addr_cap) pending (unat pending_cap)"
      using pending_addr by (simp add: bufs_disjoint_sym)
    have addr_le:
      "unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"
      using rel by (simp add: encode_window_loop_budget_rel_def)
    show ?thesis
      by (rule heap_bytes_update_disjoint_prefix[
          OF addr_pending pend_nat_lt addr_le])
  qed
  have sections_rel:
    "enc_sections_state_rel ?t data inst addr sec ?spec"
    using rel data_heap inst_heap addr_heap
    by (simp add: encode_window_loop_budget_rel_def enc_sections_state_rel_def
                  emitted_sections_def buffer_pending_byte_spec_def)
  have slack_step:
    "Suc (unat pend_len) + (unat tgt_len - Suc (unat tp)) =
     unat pend_len + (unat tgt_len - unat tp)"
    using tp_nat_lt by simp
  have data_slack:
    "unat (sections_t_C.data_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat data_cap"
    using rel unfolding encode_window_loop_budget_rel_def by blast
  have inst_slack:
    "unat (sections_t_C.inst_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat inst_cap"
    using rel unfolding encode_window_loop_budget_rel_def by blast
  have data_slack_after:
    "unat (sections_t_C.data_pos_C sec) + Suc (unat pend_len) +
       (unat tgt_len - Suc (unat tp)) + 64 \<le> unat data_cap"
    using data_slack slack_step by linarith
  have inst_slack_after:
    "unat (sections_t_C.inst_pos_C sec) + Suc (unat pend_len) +
       (unat tgt_len - Suc (unat tp)) + 64 \<le> unat inst_cap"
    using inst_slack slack_step by linarith
  have tp_eq: "enc_tp spec_st = unat tp"
    using rel by (simp add: encode_window_loop_budget_rel_def)
  have tp_spec_lt: "enc_tp spec_st < length tgt_bytes"
    using rel tp_nat_lt
    by (simp add: encode_window_loop_budget_rel_def)
  have pure_short:
    "em_len (find_best_match_spec src_bytes tgt_bytes (enc_tp spec_st)
      (build_index_spec src_bytes)) < min_match"
    by (rule encode_window_match_rel_short_spec[
        OF rel match_rel tp_lt match short])
  have budget0:
    "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap spec_st"
    using rel by (simp add: encode_window_loop_budget_rel_def)
  have budget_after:
    "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap ?spec"
    using encode_window_section_budget_buffer_pending_byte[
        OF budget0 tp_spec_lt pure_short] tp_eq
    by simp
  have rel_after:
    "encode_window_loop_budget_rel ?t src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec (tp + 1) (pend_len + 1) src_bytes tgt_bytes ?spec"
    using rel src_heap tgt_heap pending_heap sections_rel
      pend_suc tp_suc pend_nat_lt data_slack_after inst_slack_after
      tp_suc_le budget_after
    by (auto simp: encode_window_loop_budget_rel_def
                   buffer_pending_byte_spec_def word_less_nat_alt)
  have measure_after:
    "(((pend_len + 1, sec, tp + 1), ?t), ((pend_len, sec, tp), s)) \<in>
      measure
        (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
           unat tgt_len - unat tp)"
    using tp_nat_lt tp_suc by simp
  have find_run:
    "gets_the (find_best_match' src src_len tgt tgt_len tp head_arr next_arr)
      \<bullet> s \<lbrace> \<lambda>r t. t = s \<and> r = Result m \<rbrace>"
    unfolding gets_the_def
    apply runs_to_vcg
    using match by simp
  have short_branch: "match_t_C.len_C m < (4 :: 32 word)"
    using short by (simp add: min_match_def)
  have cap_branch: "\<not> pending_cap \<le> pend_len"
    using pend_lt by simp
  show ?thesis
    unfolding encode_window_c_loop_body_def
    apply simp
    apply (rule runs_to_bind)
     apply (rule runs_to_weaken[OF find_run])
    apply clarsimp
    using short_branch cap_branch
    apply simp
    apply runs_to_vcg
    using pending_ptr tgt_ptr rel_after measure_after update_eq
    apply (auto simp: update_eq)
    done
qed
subsection \<open>Pure budget-step machinery\<close>

lemma emit_inst_spec_frame_components:
  "enc_tp (emit_inst_spec sl i st) = enc_tp st"
  "enc_pending (emit_inst_spec sl i st) = enc_pending st"
  by (auto simp: emit_inst_spec_def split: prod.splits)
lemma flush_pending_spec_enc_tp:
  "enc_tp (flush_pending_spec sl st) = enc_tp st"
  by (simp add: flush_pending_spec_def emit_insts_spec_enc_tp)

lemma emit_inst_spec_sections_mono:
  "length (enc_data st) \<le> length (enc_data (emit_inst_spec sl i st)) \<and>
   length (enc_inst st) \<le> length (enc_inst (emit_inst_spec sl i st)) \<and>
   length (enc_addr st) \<le> length (enc_addr (emit_inst_spec sl i st))"
proof -
  obtain d ib ab c' f' where eq:
    "encode_one i sl (enc_flushed st) (enc_cache st)
       (enc_data st) (enc_inst st) (enc_addr st) =
     (enc_data st @ d, enc_inst st @ ib, enc_addr st @ ab, c', f')"
    by (rule encode_one_prefix)
  show ?thesis
    by (simp add: emit_inst_spec_def eq)
qed

lemma emit_insts_spec_sections_mono:
  "length (enc_data st) \<le> length (enc_data (emit_insts_spec sl insts st)) \<and>
   length (enc_inst st) \<le> length (enc_inst (emit_insts_spec sl insts st)) \<and>
   length (enc_addr st) \<le> length (enc_addr (emit_insts_spec sl insts st))"
proof (induct insts arbitrary: st)
  case Nil
  then show ?case by (simp add: emit_insts_spec_def)
next
  case (Cons i insts)
  have step:
    "emit_insts_spec sl (i # insts) st =
     emit_insts_spec sl insts (emit_inst_spec sl i st)"
    by (simp add: emit_insts_spec_def)
  show ?case
    using emit_inst_spec_sections_mono[of st sl i]
      Cons[of "emit_inst_spec sl i st"]
    by (simp add: step)
qed

lemma flush_pending_spec_sections_mono:
  "length (enc_data st) \<le> length (enc_data (flush_pending_spec sl st)) \<and>
   length (enc_inst st) \<le> length (enc_inst (flush_pending_spec sl st)) \<and>
   length (enc_addr st) \<le> length (enc_addr (flush_pending_spec sl st))"
  using emit_insts_spec_sections_mono[of st sl "flush_pending_insts (enc_pending st)"]
  by (simp add: flush_pending_spec_def)

lemma emit_copy_spec_sections_mono:
  "length (enc_data st) \<le> length (enc_data (emit_copy_spec sl a l st)) \<and>
   length (enc_inst st) \<le> length (enc_inst (emit_copy_spec sl a l st)) \<and>
   length (enc_addr st) \<le> length (enc_addr (emit_copy_spec sl a l st))"
  using emit_inst_spec_sections_mono[of st sl "RCopy a l"]
  by (simp add: emit_copy_spec_def)

lemma flush_then_emit_copy_spec_sections_mono:
  "length (enc_data st) \<le> length (enc_data (flush_then_emit_copy_spec sl a l st)) \<and>
   length (enc_inst st) \<le> length (enc_inst (flush_then_emit_copy_spec sl a l st)) \<and>
   length (enc_addr st) \<le> length (enc_addr (flush_then_emit_copy_spec sl a l st))"
proof -
  let ?st' = "if enc_pending st = [] then st else flush_pending_spec sl st"
  have flush_mono:
    "length (enc_data st) \<le> length (enc_data ?st') \<and>
     length (enc_inst st) \<le> length (enc_inst ?st') \<and>
     length (enc_addr st) \<le> length (enc_addr ?st')"
    using flush_pending_spec_sections_mono[of st sl] by simp
  show ?thesis
    using flush_mono emit_copy_spec_sections_mono[of ?st' sl a l]
    by (simp add: flush_then_emit_copy_spec_def Let_def)
qed

lemma try_emit_add_copy_spec_Some_facts:
  assumes some: "try_emit_add_copy_spec sl ca cl st = Some st'"
  shows "enc_tp st + 4 \<le> enc_tp st'
    \<and> enc_tp st' \<le> enc_tp st + cl
    \<and> length (enc_data st) \<le> length (enc_data st')
    \<and> length (enc_inst st) \<le> length (enc_inst st')
    \<and> length (enc_addr st) \<le> length (enc_addr st')"
  using some
  by (auto simp: try_emit_add_copy_spec_def fused_copy_len_spec_def
      Let_def min_match_def
      split: option.splits prod.splits if_splits)

lemma encode_window_full_step_enc_tp_progress:
  assumes tp_lt: "enc_tp st < length tgt"
  shows "enc_tp st < enc_tp (encode_window_full_step src tgt idx st)"
proof -
  let ?m = "find_best_match_spec src tgt (enc_tp st) idx"
  show ?thesis
  proof (cases "em_len ?m < min_match")
    case True
    then show ?thesis
      by (simp add: encode_window_full_step_def Let_def
          buffer_pending_byte_spec_def)
  next
    case False
    have len_ge: "min_match \<le> em_len ?m"
      using False by simp
    show ?thesis
    proof (cases "try_emit_add_copy_spec (length src) (em_pos ?m)
        (em_len ?m) st")
      case None
      have tp_eq:
        "enc_tp (encode_window_full_step src tgt idx st) =
         enc_tp st + em_len ?m"
      proof -
        let ?st1 = "if enc_pending st = [] then st
                    else flush_pending_spec (length src) st"
        have tp1: "enc_tp ?st1 = enc_tp st"
          by (simp add: flush_pending_spec_enc_tp)
        show ?thesis
          using False None tp1
          by (simp add: encode_window_full_step_def Let_def
              flush_then_emit_copy_spec_def emit_copy_spec_def
              emit_inst_spec_frame_components)
      qed
      show ?thesis
        using tp_eq len_ge by (simp add: min_match_def)
    next
      case (Some fused)
      have fused_facts:
        "enc_tp st + 4 \<le> enc_tp fused"
        using try_emit_add_copy_spec_Some_facts[OF Some] by simp
      show ?thesis
        using False Some fused_facts
        by (auto simp: encode_window_full_step_def Let_def
            emit_copy_spec_def emit_inst_spec_frame_components)
    qed
  qed
qed

lemma encode_window_full_step_match_tp_le:
  assumes tp_lt: "enc_tp st < length tgt"
      and not_short:
        "\<not> em_len (find_best_match_spec src tgt (enc_tp st)
              (build_index_spec src)) < min_match"
  shows "enc_tp (encode_window_full_step src tgt (build_index_spec src) st)
           \<le> length tgt"
proof -
  let ?m = "find_best_match_spec src tgt (enc_tp st) (build_index_spec src)"
  have match_min: "min_match \<le> em_len ?m"
    using not_short by simp
  have sound: "enc_tp st + em_len ?m \<le> length tgt"
    using find_best_match_spec_sound[OF refl match_min] by simp
  show ?thesis
  proof (cases "try_emit_add_copy_spec (length src) (em_pos ?m) (em_len ?m) st")
    case None
    then show ?thesis
      using not_short sound
      by (simp add: encode_window_full_step_def Let_def
          flush_then_emit_copy_spec_def emit_copy_spec_def
          flush_pending_spec_enc_tp emit_inst_spec_frame_components)
  next
    case (Some fused)
    have consumed_le: "enc_tp fused \<le> enc_tp st + em_len ?m"
      and tp_ge: "enc_tp st + 4 \<le> enc_tp fused"
      using try_emit_add_copy_spec_Some_facts[OF Some] by simp_all
    show ?thesis
    proof (cases "enc_tp fused - enc_tp st < em_len ?m")
      case True
      have "enc_tp (encode_window_full_step src tgt (build_index_spec src) st)
              = enc_tp fused + (em_len ?m - (enc_tp fused - enc_tp st))"
        using not_short Some True
        by (simp add: encode_window_full_step_def Let_def
            emit_copy_spec_def emit_inst_spec_frame_components)
      also have "\<dots> = enc_tp st + em_len ?m"
        using consumed_le tp_ge by simp
      finally show ?thesis using sound by simp
    next
      case False
      have "enc_tp (encode_window_full_step src tgt (build_index_spec src) st)
              = enc_tp fused"
        using not_short Some False
        by (simp add: encode_window_full_step_def Let_def)
      then show ?thesis using consumed_le sound by simp
    qed
  qed
qed

lemma encode_window_full_loop_fuel_stable:
  "length tgt - enc_tp st < a \<Longrightarrow>
   length tgt - enc_tp st < b \<Longrightarrow>
   encode_window_full_loop a src tgt (build_index_spec src) st =
   encode_window_full_loop b src tgt (build_index_spec src) st"
proof (induct a arbitrary: st b)
  case 0
  then show ?case by simp
next
  case (Suc a)
  show ?case
  proof (cases "length tgt \<le> enc_tp st")
    case True
    then obtain b' where b_eq: "b = Suc b'"
      using Suc.prems(2) by (cases b) auto
    show ?thesis
      using True b_eq by simp
  next
    case False
    hence tp_lt: "enc_tp st < length tgt" by simp
    obtain b' where b_eq: "b = Suc b'"
      using Suc.prems(2) tp_lt by (cases b) auto
    let ?st' = "encode_window_full_step src tgt (build_index_spec src) st"
    have prog: "enc_tp st < enc_tp ?st'"
      by (rule encode_window_full_step_enc_tp_progress[OF tp_lt])
    have le_a: "length tgt - enc_tp st \<le> a"
      using Suc.prems(1) by simp
    have le_b: "length tgt - enc_tp st \<le> b'"
      using Suc.prems(2) b_eq by simp
    have a_pos: "0 < a"
      using tp_lt le_a by simp
    have b'_pos: "0 < b'"
      using tp_lt le_b by simp
    have next_a: "length tgt - enc_tp ?st' < a"
    proof (cases "enc_tp ?st' \<le> length tgt")
      case True
      then show ?thesis using prog le_a by simp
    next
      case False
      then show ?thesis using a_pos by simp
    qed
    have next_b: "length tgt - enc_tp ?st' < b'"
    proof (cases "enc_tp ?st' \<le> length tgt")
      case True
      then show ?thesis using prog le_b by simp
    next
      case False
      then show ?thesis using b'_pos by simp
    qed
    have "encode_window_full_loop (Suc a) src tgt (build_index_spec src) st =
          encode_window_full_loop a src tgt (build_index_spec src) ?st'"
      using tp_lt by (simp add: encode_window_full_step_def Let_def)
    also have "\<dots> = encode_window_full_loop b' src tgt (build_index_spec src) ?st'"
      by (rule Suc.hyps[OF next_a next_b])
    also have "\<dots> = encode_window_full_loop b src tgt (build_index_spec src) st"
      using tp_lt b_eq by (simp add: encode_window_full_step_def Let_def)
    finally show ?thesis .
  qed
qed

lemma encode_window_full_loop_sections_mono:
  "length (enc_data st) \<le>
     length (enc_data (encode_window_full_loop n src tgt idx st)) \<and>
   length (enc_inst st) \<le>
     length (enc_inst (encode_window_full_loop n src tgt idx st)) \<and>
   length (enc_addr st) \<le>
     length (enc_addr (encode_window_full_loop n src tgt idx st))"
proof (induct n arbitrary: st)
  case 0
  show ?case
    using flush_pending_spec_sections_mono[of st "length src"]
    by (auto split: if_splits)
next
  case (Suc n)
  show ?case
  proof (cases "length tgt \<le> enc_tp st")
    case True
    then show ?thesis
      using flush_pending_spec_sections_mono[of st "length src"]
      by simp
  next
    case False
    let ?st' = "encode_window_full_step src tgt idx st"
    have step_mono:
      "length (enc_data st) \<le> length (enc_data ?st') \<and>
       length (enc_inst st) \<le> length (enc_inst ?st') \<and>
       length (enc_addr st) \<le> length (enc_addr ?st')"
    proof (cases "em_len (find_best_match_spec src tgt (enc_tp st) idx)
        < min_match")
      case True
      then show ?thesis
        by (auto simp: encode_window_full_step_def Let_def
            buffer_pending_byte_spec_def)
    next
      case notshort: False
      let ?m = "find_best_match_spec src tgt (enc_tp st) idx"
      show ?thesis
      proof (cases "try_emit_add_copy_spec (length src) (em_pos ?m)
          (em_len ?m) st")
        case None
        then show ?thesis
          using notshort
            flush_then_emit_copy_spec_sections_mono[of st "length src"
              "em_pos ?m" "em_len ?m"]
          by (simp add: encode_window_full_step_def Let_def)
      next
        case (Some fused)
        have f_mono:
          "length (enc_data st) \<le> length (enc_data fused) \<and>
           length (enc_inst st) \<le> length (enc_inst fused) \<and>
           length (enc_addr st) \<le> length (enc_addr fused)"
          using try_emit_add_copy_spec_Some_facts[OF Some] by simp
        show ?thesis
          using notshort Some f_mono
            emit_copy_spec_sections_mono[of fused "length src"
              "em_pos ?m + (enc_tp fused - enc_tp st)"
              "em_len ?m - (enc_tp fused - enc_tp st)"]
          by (auto simp: encode_window_full_step_def Let_def)
      qed
    qed
    have "encode_window_full_loop (Suc n) src tgt idx st =
          encode_window_full_loop n src tgt idx ?st'"
      using False by (subst encode_window_full_loop_Suc) simp
    then show ?thesis
      using step_mono Suc.hyps[of ?st'] by (simp; linarith?)
  qed
qed

lemma encode_window_section_budget_match_step:
  assumes budget:
    "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap spec_st"
      and tp_lt: "enc_tp spec_st < length tgt_bytes"
      and not_short:
        "\<not> em_len (find_best_match_spec src_bytes tgt_bytes (enc_tp spec_st)
              (build_index_spec src_bytes)) < min_match"
      and step_eq:
        "spec_st' = encode_window_full_step src_bytes tgt_bytes
           (build_index_spec src_bytes) spec_st"
  shows "encode_window_section_budget src_bytes tgt_bytes
           data_cap inst_cap addr_cap spec_st'"
proof -
  let ?idx = "build_index_spec src_bytes"
  let ?final = "encode_window_final_spec_state src_bytes tgt_bytes"
  have reaches0:
    "encode_window_full_loop (length tgt_bytes + 1 - enc_tp spec_st)
       src_bytes tgt_bytes ?idx spec_st = ?final"
    using budget
    by (simp add: encode_window_section_budget_def
        encode_window_spec_reaches_final_def)
  have tp'_le: "enc_tp spec_st' \<le> length tgt_bytes"
    using step_eq encode_window_full_step_match_tp_le[OF tp_lt not_short]
    by simp
  have prog: "enc_tp spec_st < enc_tp spec_st'"
    using step_eq encode_window_full_step_enc_tp_progress[OF tp_lt] by simp
  have fuel_eq: "length tgt_bytes + 1 - enc_tp spec_st =
                 Suc (length tgt_bytes - enc_tp spec_st)"
    using tp_lt by simp
  have step_unfold:
    "encode_window_full_loop (length tgt_bytes - enc_tp spec_st)
       src_bytes tgt_bytes ?idx spec_st' = ?final"
  proof -
    have "?final =
          encode_window_full_loop (Suc (length tgt_bytes - enc_tp spec_st))
            src_bytes tgt_bytes ?idx spec_st"
      using reaches0 fuel_eq by simp
    also have "\<dots> =
          encode_window_full_loop (length tgt_bytes - enc_tp spec_st)
            src_bytes tgt_bytes ?idx
            (encode_window_full_step src_bytes tgt_bytes ?idx spec_st)"
      using tp_lt by (subst encode_window_full_loop_Suc) simp
    finally show ?thesis using step_eq by simp
  qed
  have f_gt: "length tgt_bytes - enc_tp spec_st' <
              length tgt_bytes - enc_tp spec_st"
  proof (cases "enc_tp spec_st' \<le> length tgt_bytes")
    case True
    then show ?thesis using prog by simp
  next
    case False
    then show ?thesis using tp_lt by simp
  qed
  have g_gt: "length tgt_bytes - enc_tp spec_st' <
              length tgt_bytes + 1 - enc_tp spec_st'"
    using tp'_le by simp
  have reaches':
    "encode_window_full_loop (length tgt_bytes + 1 - enc_tp spec_st')
       src_bytes tgt_bytes ?idx spec_st' = ?final"
    using step_unfold
      encode_window_full_loop_fuel_stable[
        where src = src_bytes and tgt = tgt_bytes
          and st = spec_st'
          and a = "length tgt_bytes - enc_tp spec_st"
          and b = "length tgt_bytes + 1 - enc_tp spec_st'"]
      f_gt g_gt
    by simp
  have reaches_final':
    "encode_window_spec_reaches_final src_bytes tgt_bytes spec_st'"
    using reaches' by (simp add: encode_window_spec_reaches_final_def)
  have step_sections_le_final:
    "length (enc_data spec_st') \<le> length (enc_data ?final) \<and>
     length (enc_inst spec_st') \<le> length (enc_inst ?final) \<and>
     length (enc_addr spec_st') \<le> length (enc_addr ?final)"
    using reaches'
      encode_window_full_loop_sections_mono[
        where n = "length tgt_bytes + 1 - enc_tp spec_st'"
          and src = src_bytes and tgt = tgt_bytes and idx = ?idx
          and st = spec_st']
    by simp
  have prefix':
    "encode_window_section_prefix_budget src_bytes tgt_bytes spec_st'"
    using step_sections_le_final
    by (simp add: encode_window_section_prefix_budget_def)
  have caps:
    "encoder_final_section_caps_ok src_bytes tgt_bytes
      data_cap inst_cap addr_cap"
    using budget by (simp add: encode_window_section_budget_def)
  show ?thesis
    using reaches_final' prefix' caps
    by (simp add: encode_window_section_budget_def)
qed


subsection \<open>Reusable flush_pending' helper for the loop context\<close>

lemma encode_window_loop_buffers_ok_pending_ptr_valid:
  fixes len :: "32 word"
  assumes buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and len_le: "unat len \<le> unat pending_cap"
  shows "\<forall>j < unat len.
      ptr_valid (heap_typing s)
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
proof (intro allI impI)
  fix j
  assume j_lt: "j < unat len"
  have pending_ok: "buf_valid s pending (unat pending_cap)"
    using buffers by (simp add: encode_window_loop_buffers_ok_def)
  have no_overflow: "unat (0 :: 32 word) + unat len < 2 ^ 32"
    using unat_lt2p[of len] by simp
  have range: "unat (0 :: 32 word) + unat len \<le> unat pending_cap"
    using len_le by simp
  show "ptr_valid (heap_typing s)
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
    by (rule buf_valid_word_rangeD[OF pending_ok j_lt no_overflow range])
qed

lemma flush_pending'_loop_from_final_fits:
  fixes s :: lifted_globals
    and src tgt data inst addr pending :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap pend_len :: "32 word"
  assumes buffers:
      "encode_window_loop_buffers_ok s src src_len tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and pending_eq:
      "enc_pending spec_st = heap_bytes_word s pending 0 pend_len"
    and pend_len_le: "unat pend_len \<le> unat pending_cap"
    and final_data_room64:
      "length (enc_data (flush_pending_spec sl spec_st)) + 64 \<le> unat data_cap"
    and final_inst_room64:
      "length (enc_inst (flush_pending_spec sl spec_st)) + 64 \<le> unat inst_cap"
    and final_addr_room64:
      "length (enc_addr (flush_pending_spec sl spec_st)) + 64 \<le> unat addr_cap"
  shows "flush_pending' sec data data_cap inst inst_cap pending pend_len \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec'.
              r = Result sec' \<and>
              enc_sections_state_rel t data inst addr sec'
                (flush_pending_spec sl spec_st) \<and>
              sections_t_C.err_C sec' = ENC_OK \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?pending_bytes = "heap_bytes_word s pending 0 pend_len"
  let ?final_st = "flush_pending_spec sl spec_st"
  have typing_s0: "heap_typing s = heap_typing s"
    by (rule refl)
  have pending_valid:
    "\<forall>j < unat pend_len.
      ptr_valid (heap_typing s)
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
    by (rule encode_window_loop_buffers_ok_pending_ptr_valid[
        OF buffers pend_len_le])
  have final_loop:
    "flush_pending_loop_spec sl ?pending_bytes 0 0 spec_st = ?final_st"
    by (rule flush_pending_loop_spec_eq_flush_pending_spec[OF pending_eq])
    have tail_pre:
      "\<And>add_start i sec_cur t loop_st. \<lbrakk>
        flush_pending_outer_loop_inv (sl) s data inst addr
          pending pend_len spec_st add_start i sec_cur t;
        i \<le> pend_len;
        i = pend_len;
        enc_sections_state_rel t data inst addr sec_cur loop_st;
        flush_pending_loop_spec (sl)
          (heap_bytes_word s pending 0 pend_len) (unat add_start)
          (unat pend_len) loop_st =
        flush_pending_loop_spec (sl)
          (heap_bytes_word s pending 0 pend_len) 0 0 spec_st
      \<rbrakk> \<Longrightarrow>
        flush_pending_outer_tail data data_cap inst inst_cap pending pend_len
          add_start sec_cur \<bullet> t
        \<lbrace> \<lambda>Res sec' u.
	             enc_sections_state_rel u data inst addr sec'
	               (flush_pending_outer_tail_state (sl) s
	                 pending pend_len add_start loop_st) \<and>
	             sections_t_C.err_C sec' = ENC_OK \<and>
	             heap_typing u = heap_typing s \<rbrace>"
    proof -
      fix add_start i sec_cur t loop_st
      assume inv:
        "flush_pending_outer_loop_inv (sl) s data inst addr
          pending pend_len spec_st add_start i sec_cur t"
      assume i_eq: "i = pend_len"
      assume rel_cur: "enc_sections_state_rel t data inst addr sec_cur loop_st"
      assume eq_loop:
        "flush_pending_loop_spec (sl)
          (heap_bytes_word s pending 0 pend_len) (unat add_start)
          (unat pend_len) loop_st =
        flush_pending_loop_spec (sl)
          (heap_bytes_word s pending 0 pend_len) 0 0 spec_st"
      have add_start_le_len: "add_start \<le> pend_len"
        using inv i_eq by (simp add: flush_pending_outer_loop_inv_def)
      have typing_t_s: "heap_typing t = heap_typing s"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have typing_t_s0: "heap_typing t = heap_typing s"
        using typing_t_s typing_s0 by simp
      have frame_t:
        "heap_bytes_word t pending 0 pend_len = ?pending_bytes"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have sec_cur_ok: "sections_t_C.err_C sec_cur = ENC_OK"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have exit_tail:
        "flush_pending_loop_spec (sl) ?pending_bytes
          (unat add_start) (unat pend_len) loop_st =
         flush_pending_outer_tail_state (sl) s pending
          pend_len add_start loop_st"
        unfolding flush_pending_outer_tail_state_def
        by (rule flush_pending_loop_spec_exit_heap_emit_word[
          OF add_start_le_len]) simp
      have tail_state_eq:
        "flush_pending_outer_tail_state (sl) s pending
          pend_len add_start loop_st = ?final_st"
        using exit_tail eq_loop final_loop by simp
      have add_start_nat_le_len: "unat add_start \<le> unat pend_len"
        using add_start_le_len by (simp add: word_le_nat_alt)
      have pend_nat_le_pending_bytes: "unat pend_len \<le> length ?pending_bytes"
        by simp
      have cur_data_le_loop:
        "length (enc_data loop_st) \<le>
         length (enc_data
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat add_start) (unat pend_len) loop_st))"
        by (rule flush_pending_loop_spec_mono(1)[
          OF add_start_nat_le_len pend_nat_le_pending_bytes])
      have cur_inst_le_loop:
        "length (enc_inst loop_st) \<le>
         length (enc_inst
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat add_start) (unat pend_len) loop_st))"
        by (rule flush_pending_loop_spec_mono(2)[
          OF add_start_nat_le_len pend_nat_le_pending_bytes])
      have cur_addr_eq_loop:
        "length (enc_addr
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat add_start) (unat pend_len) loop_st)) =
         length (enc_addr loop_st)"
        by (rule flush_pending_loop_spec_mono(3)[
          OF add_start_nat_le_len pend_nat_le_pending_bytes])
      have cur_data_le_final:
        "length (enc_data loop_st) \<le> length (enc_data ?final_st)"
        using cur_data_le_loop eq_loop final_loop by simp
      have cur_inst_le_final:
        "length (enc_inst loop_st) \<le> length (enc_inst ?final_st)"
        using cur_inst_le_loop eq_loop final_loop by simp
      have cur_addr_le_final:
        "length (enc_addr loop_st) = length (enc_addr ?final_st)"
        using cur_addr_eq_loop eq_loop final_loop by simp
      show "flush_pending_outer_tail data data_cap inst inst_cap pending
          pend_len add_start sec_cur \<bullet> t
        \<lbrace> \<lambda>Res sec' u.
	             enc_sections_state_rel u data inst addr sec'
	               (flush_pending_outer_tail_state (sl) s
	                 pending pend_len add_start loop_st) \<and>
	             sections_t_C.err_C sec' = ENC_OK \<and>
	             heap_typing u = heap_typing s \<rbrace>"
      proof (cases "add_start < pend_len")
        case False
	        show ?thesis
	          using False rel_cur typing_t_s sec_cur_ok
	          by (auto simp: flush_pending_outer_tail_def
	              flush_pending_outer_tail_state_def enc_sections_state_rel_def)
      next
        case add_lt: True
        let ?sz = "pend_len - add_start"
        let ?add_state =
          "emit_inst_spec (sl)
            (RAdd (heap_bytes_word s pending add_start ?sz)) loop_st"
        have add_pending_clear:
          "?add_state\<lparr>enc_pending := []\<rparr> = ?final_st"
          using tail_state_eq add_lt
          by (simp add: flush_pending_outer_tail_state_def)
        have add_sections_final:
          "enc_data ?add_state = enc_data ?final_st"
          "enc_inst ?add_state = enc_inst ?final_st"
          "enc_addr ?add_state = enc_addr ?final_st"
          using arg_cong[OF add_pending_clear, of enc_data]
            arg_cong[OF add_pending_clear, of enc_inst]
            arg_cong[OF add_pending_clear, of enc_addr]
          by simp_all
        have sz_ge: "(1 :: 32 word) \<le> ?sz"
          using add_lt by unat_arith
        have pending_range:
          "unat add_start + unat ?sz \<le> unat pending_cap"
          using add_start_le_len pend_len_le by unat_arith
        have slice_eq:
          "heap_bytes_word t pending add_start ?sz =
           heap_bytes_word s pending add_start ?sz"
          by (rule heap_bytes_word_slice_eq_from_zero_frame[
            OF frame_t]) (use add_start_le_len in unat_arith)
        have data_room_add:
          "unat (sections_t_C.data_pos_C sec_cur) + unat ?sz \<le>
           unat data_cap"
        proof -
          have add_len:
            "length (enc_data ?add_state) =
             unat (sections_t_C.data_pos_C sec_cur) + unat ?sz"
            using enc_sections_state_rel_lengths(1)[OF rel_cur] add_lt
            by (simp add: emit_inst_spec_RAdd_sections_general)
          have "length (enc_data ?add_state) =
                length (enc_data ?final_st)"
            using add_sections_final(1) by simp
          then show ?thesis
            using add_len final_data_room64 by linarith
        qed
        have inst_room_add:
          "unat (sections_t_C.inst_pos_C sec_cur) + 6 \<le>
           unat inst_cap"
          using enc_sections_state_rel_lengths(2)[OF rel_cur]
            cur_inst_le_final final_inst_room64 by linarith
        have addr_room_add:
          "unat (sections_t_C.addr_pos_C sec_cur) \<le> unat addr_cap"
          using enc_sections_state_rel_lengths(3)[OF rel_cur]
            cur_addr_le_final final_addr_room64 by linarith
        have add:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?add_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t \<rbrace>"
          apply (rule runs_to_weaken)
           apply (rule emit_pending_add_chunk_from_loop_buffers[
            where spec_src_len = "sl"
              and pending_frame_off = 0
              and pending_frame_len = pend_len])
                    apply (rule buffers)
                   apply (rule typing_t_s0)
                  apply (rule rel_cur)
                 apply (rule sec_cur_ok)
                apply (rule sz_ge)
               apply (rule pending_range)
              apply (simp add: pend_len_le)
             apply (rule data_room_add)
            apply (rule inst_room_add)
           apply (rule addr_room_add)
          using slice_eq by auto
        show ?thesis
          unfolding flush_pending_outer_tail_def
          using add_lt
          apply simp
          apply (rule runs_to_weaken[OF add])
          using typing_t_s frame_t tail_state_eq add_lt add_sections_final
          apply (auto simp: flush_pending_outer_tail_state_def
              enc_sections_state_rel_def)
          done
      qed
    qed
    have run_pre:
      "\<And>add_start i sec_cur t j b loop_st. \<lbrakk>
        flush_pending_outer_loop_inv (sl) s data inst addr
          pending pend_len spec_st add_start i sec_cur t;
        i \<le> pend_len;
        i < j;
        j \<le> pend_len;
        pending_run_end (heap_bytes_word s pending 0 pend_len) (unat i) =
          unat j;
        (4 :: 32 word) \<le> j - i;
        b = heap_w8 s (pending +\<^sub>p uint i);
        enc_sections_state_rel t data inst addr sec_cur loop_st;
        flush_pending_loop_spec (sl)
          (heap_bytes_word s pending 0 pend_len) (unat add_start) (unat i)
          loop_st =
        flush_pending_loop_spec (sl)
          (heap_bytes_word s pending 0 pend_len) 0 0 spec_st
      \<rbrakk> \<Longrightarrow>
        flush_pending_outer_run_branch data data_cap inst inst_cap pending
          add_start i j b sec_cur \<bullet> t
        \<lbrace> \<lambda>r u.
             \<exists>sec'.
               r = Result (j, j, sec') \<and>
               sections_t_C.err_C sec' = ENC_OK \<and>
               heap_bytes_word u pending 0 pend_len =
                 heap_bytes_word s pending 0 pend_len \<and>
               heap_typing u = heap_typing s \<and>
               enc_sections_state_rel u data inst addr sec'
                 (flush_pending_outer_run_state (sl) s
                   pending add_start i j b loop_st) \<rbrace>"
    proof -
      fix add_start i sec_cur t j b loop_st
      assume inv:
        "flush_pending_outer_loop_inv (sl) s data inst addr
          pending pend_len spec_st add_start i sec_cur t"
      assume i_le_len: "i \<le> pend_len"
        and i_lt_j: "i < j"
        and j_le_len: "j \<le> pend_len"
        and run_end:
          "pending_run_end (heap_bytes_word s pending 0 pend_len) (unat i) =
           unat j"
        and run_ge: "(4 :: 32 word) \<le> j - i"
        and b_eq: "b = heap_w8 s (pending +\<^sub>p uint i)"
        and rel_cur: "enc_sections_state_rel t data inst addr sec_cur loop_st"
        and eq_loop:
          "flush_pending_loop_spec (sl)
            (heap_bytes_word s pending 0 pend_len) (unat add_start)
            (unat i) loop_st =
           flush_pending_loop_spec (sl)
            (heap_bytes_word s pending 0 pend_len) 0 0 spec_st"
      have add_start_le_i: "add_start \<le> i"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have typing_t_s: "heap_typing t = heap_typing s"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have typing_t_s0: "heap_typing t = heap_typing s"
        using typing_t_s typing_s0 by simp
      have frame_t:
        "heap_bytes_word t pending 0 pend_len = ?pending_bytes"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have sec_cur_ok: "sections_t_C.err_C sec_cur = ENC_OK"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have add_start_nat_le_i: "unat add_start \<le> unat i"
        using add_start_le_i by (simp add: word_le_nat_alt)
      have i_nat_le_pending_bytes: "unat i \<le> length ?pending_bytes"
        using i_le_len by (simp add: word_le_nat_alt)
      have j_nat_le_pending_bytes: "unat j \<le> length ?pending_bytes"
        using j_le_len by (simp add: word_le_nat_alt)
      have cur_data_le_loop:
        "length (enc_data loop_st) \<le>
         length (enc_data
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat add_start) (unat i) loop_st))"
        by (rule flush_pending_loop_spec_mono(1)[
          OF add_start_nat_le_i i_nat_le_pending_bytes])
      have cur_inst_le_loop:
        "length (enc_inst loop_st) \<le>
         length (enc_inst
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat add_start) (unat i) loop_st))"
        by (rule flush_pending_loop_spec_mono(2)[
          OF add_start_nat_le_i i_nat_le_pending_bytes])
      have cur_addr_eq_loop:
        "length (enc_addr
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat add_start) (unat i) loop_st)) =
         length (enc_addr loop_st)"
        by (rule flush_pending_loop_spec_mono(3)[
          OF add_start_nat_le_i i_nat_le_pending_bytes])
      have cur_data_le_final:
        "length (enc_data loop_st) \<le> length (enc_data ?final_st)"
        using cur_data_le_loop eq_loop final_loop by simp
      have cur_inst_le_final:
        "length (enc_inst loop_st) \<le> length (enc_inst ?final_st)"
        using cur_inst_le_loop eq_loop final_loop by simp
      have cur_addr_eq_final:
        "length (enc_addr loop_st) = length (enc_addr ?final_st)"
        using cur_addr_eq_loop eq_loop final_loop by simp
      let ?add_base =
        "if add_start < i
         then emit_inst_spec (sl)
           (RAdd (heap_bytes_word s pending add_start (i - add_start)))
           loop_st
         else loop_st"
      let ?run_state =
        "flush_pending_outer_run_state (sl) s pending
          add_start i j b loop_st"
      have step_eq:
        "flush_pending_loop_spec (sl) ?pending_bytes
          (unat add_start) (unat i) loop_st =
         flush_pending_loop_spec (sl) ?pending_bytes
          (unat j) (unat j) ?run_state"
        unfolding flush_pending_outer_run_state_def
        by (rule flush_pending_loop_spec_run_step_heap_emit_word[
          OF add_start_le_i i_lt_j j_le_len run_end run_ge b_eq])
      have run_loop_eq:
        "flush_pending_loop_spec (sl) ?pending_bytes
          (unat j) (unat j) ?run_state = ?final_st"
        using step_eq eq_loop final_loop by simp
      have run_state_data_le_loop:
        "length (enc_data ?run_state) \<le>
         length (enc_data
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat j) (unat j) ?run_state))"
        by (rule flush_pending_loop_spec_mono(1)[
          OF order_refl j_nat_le_pending_bytes])
      have run_state_inst_le_loop:
        "length (enc_inst ?run_state) \<le>
         length (enc_inst
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat j) (unat j) ?run_state))"
        by (rule flush_pending_loop_spec_mono(2)[
          OF order_refl j_nat_le_pending_bytes])
      have run_state_addr_eq_loop:
        "length (enc_addr
          (flush_pending_loop_spec (sl) ?pending_bytes
            (unat j) (unat j) ?run_state)) =
         length (enc_addr ?run_state)"
        by (rule flush_pending_loop_spec_mono(3)[
          OF order_refl j_nat_le_pending_bytes])
      have run_state_data_le_final:
        "length (enc_data ?run_state) \<le> length (enc_data ?final_st)"
        using run_state_data_le_loop run_loop_eq by simp
      have run_state_inst_le_final:
        "length (enc_inst ?run_state) \<le> length (enc_inst ?final_st)"
        using run_state_inst_le_loop run_loop_eq by simp
      have run_state_addr_eq_final:
        "length (enc_addr ?run_state) = length (enc_addr ?final_st)"
        using run_state_addr_eq_loop run_loop_eq by simp
      have run_len_ge_nat: "4 \<le> unat (j - i)"
        using run_ge by (simp add: word_le_nat_alt)
      have add_base_data_plus:
        "length (enc_data ?run_state) = length (enc_data ?add_base) + 1"
        unfolding flush_pending_outer_run_state_def
        using run_len_ge_nat
        by (simp add: emit_inst_spec_RRun_sections_general)
      show "flush_pending_outer_run_branch data data_cap inst inst_cap pending
          add_start i j b sec_cur \<bullet> t
        \<lbrace> \<lambda>r u.
             \<exists>sec'.
               r = Result (j, j, sec') \<and>
               sections_t_C.err_C sec' = ENC_OK \<and>
               heap_bytes_word u pending 0 pend_len =
                 heap_bytes_word s pending 0 pend_len \<and>
               heap_typing u = heap_typing s \<and>
               enc_sections_state_rel u data inst addr sec'
                 ?run_state \<rbrace>"
      proof (cases "add_start < i")
        case no_add: False
        have data_room_run:
          "unat (sections_t_C.data_pos_C sec_cur) + 1 \<le> unat data_cap"
          using enc_sections_state_rel_lengths(1)[OF rel_cur]
            cur_data_le_final final_data_room64 by linarith
        have inst_room_run:
          "unat (sections_t_C.inst_pos_C sec_cur) + 6 \<le> unat inst_cap"
          using enc_sections_state_rel_lengths(2)[OF rel_cur]
            cur_inst_le_final final_inst_room64 by linarith
        have addr_room_run:
          "unat (sections_t_C.addr_pos_C sec_cur) \<le> unat addr_cap"
          using enc_sections_state_rel_lengths(3)[OF rel_cur]
            cur_addr_eq_final final_addr_room64 by linarith
        have run:
          "emit_run' sec_cur data data_cap inst inst_cap b (j - i) \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?run_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t \<rbrace>"
          unfolding flush_pending_outer_run_state_def
          using no_add
          apply simp
	          apply (rule emit_pending_run_chunk_from_loop_buffers[
	            where spec_src_len = "sl"
	              and pending_frame_off = 0
	              and pending_frame_len = pend_len])
                   apply (rule buffers)
                  apply (rule typing_t_s0)
                 apply (rule rel_cur)
                apply (rule sec_cur_ok)
               apply (simp add: pend_len_le)
              apply (rule data_room_run)
             apply (rule inst_room_run)
            apply (rule addr_room_run)
          done
        show ?thesis
          unfolding flush_pending_outer_run_branch_def
          using no_add
          apply simp
          apply (rule runs_to_bind_exception)
           apply (rule runs_to_liftE)
           apply (rule runs_to_weaken[OF run])
          using frame_t typing_t_s
          apply auto
          done
      next
        case add_lt: True
        let ?sz = "i - add_start"
        let ?add_state =
          "emit_inst_spec (sl)
            (RAdd (heap_bytes_word s pending add_start ?sz)) loop_st"
        have sz_ge: "(1 :: 32 word) \<le> ?sz"
          using add_lt by unat_arith
        have pending_range:
          "unat add_start + unat ?sz \<le> unat pending_cap"
          using add_start_le_i i_le_len pend_len_le by unat_arith
        have slice_eq:
          "heap_bytes_word t pending add_start ?sz =
           heap_bytes_word s pending add_start ?sz"
          by (rule heap_bytes_word_slice_eq_from_zero_frame[
            OF frame_t]) (use add_start_le_i i_le_len in unat_arith)
        have add_state_eq_base:
          "?add_state = ?add_base"
          using add_lt by simp
        have add_base_inst_le_run:
          "length (enc_inst ?add_base) \<le> length (enc_inst ?run_state)"
          unfolding flush_pending_outer_run_state_def
          by (simp add: emit_inst_spec_RRun_sections_general)
        have add_base_inst_len:
          "length (enc_inst ?add_base) = length (enc_inst ?add_state)"
          using add_state_eq_base by simp
        have add_state_inst_le_final:
          "length (enc_inst ?add_state) \<le> length (enc_inst ?final_st)"
          using add_base_inst_le_run add_base_inst_len
            run_state_inst_le_final by linarith
        have add_state_addr_eq_final:
          "length (enc_addr ?add_state) = length (enc_addr ?final_st)"
          using add_state_eq_base run_state_addr_eq_final
          unfolding flush_pending_outer_run_state_def
          by (simp add: emit_inst_spec_RRun_sections_general)
        have add_data_room:
          "unat (sections_t_C.data_pos_C sec_cur) + unat ?sz \<le>
           unat data_cap"
        proof -
          have add_len:
            "length (enc_data ?add_state) =
             unat (sections_t_C.data_pos_C sec_cur) + unat ?sz"
            using enc_sections_state_rel_lengths(1)[OF rel_cur] add_lt
            by (simp add: emit_inst_spec_RAdd_sections_general)
          have add_base_data_len:
            "length (enc_data ?add_base) = length (enc_data ?add_state)"
            using add_state_eq_base by simp
          have add_state_plus_le_final:
            "length (enc_data ?add_state) + 1 \<le>
             length (enc_data ?final_st)"
            using add_base_data_plus run_state_data_le_final
              add_base_data_len by linarith
          have "length (enc_data ?add_state) \<le>
                length (enc_data ?final_st)"
            using add_state_plus_le_final by linarith
          then show ?thesis
            using add_len final_data_room64 by linarith
        qed
        have add_inst_room:
          "unat (sections_t_C.inst_pos_C sec_cur) + 6 \<le>
           unat inst_cap"
          using enc_sections_state_rel_lengths(2)[OF rel_cur]
            cur_inst_le_final final_inst_room64 by linarith
        have add_addr_room:
          "unat (sections_t_C.addr_pos_C sec_cur) \<le> unat addr_cap"
          using enc_sections_state_rel_lengths(3)[OF rel_cur]
            cur_addr_eq_final final_addr_room64 by linarith
        have add:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?add_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t \<rbrace>"
          apply (rule runs_to_weaken)
           apply (rule emit_pending_add_chunk_from_loop_buffers[
            where spec_src_len = "sl"
              and pending_frame_off = 0
              and pending_frame_len = pend_len])
                    apply (rule buffers)
                   apply (rule typing_t_s0)
                  apply (rule rel_cur)
                 apply (rule sec_cur_ok)
                apply (rule sz_ge)
               apply (rule pending_range)
              apply (simp add: pend_len_le)
             apply (rule add_data_room)
            apply (rule add_inst_room)
           apply (rule add_addr_room)
          using slice_eq by auto
        have add_run_data_room:
          "\<And>u sec_add. enc_sections_state_rel u data inst addr sec_add
              ?add_state \<Longrightarrow>
            unat (sections_t_C.data_pos_C sec_add) + 1 \<le>
              unat data_cap"
          using add_base_data_plus run_state_data_le_final add_state_eq_base
            final_data_room64
          by (simp add: enc_sections_state_rel_lengths)
        have add_run_inst_room:
          "\<And>u sec_add. enc_sections_state_rel u data inst addr sec_add
              ?add_state \<Longrightarrow>
            unat (sections_t_C.inst_pos_C sec_add) + 6 \<le>
              unat inst_cap"
          using add_state_inst_le_final final_inst_room64
          by (simp add: enc_sections_state_rel_lengths; linarith)
	        have add_run_addr_room:
	          "\<And>u sec_add. enc_sections_state_rel u data inst addr sec_add
	              ?add_state \<Longrightarrow>
	            unat (sections_t_C.addr_pos_C sec_add) \<le> unat addr_cap"
	          using final_addr_room64 add_state_addr_eq_final
	          by (simp add: enc_sections_state_rel_lengths; linarith)
	        have add_checked:
	          "(do {
	              sec_add \<leftarrow> liftE
	                (emit_add' sec_cur data data_cap inst inst_cap pending
	                  add_start ?sz);
	              unless (sections_t_C.err_C sec_add = ENC_OK)
	                (throw sec_add);
	              return sec_add
	            }) \<bullet> t
	           \<lbrace> \<lambda>r u.
	                \<exists>sec_add.
	                  r = Result sec_add \<and>
	                  sections_t_C.err_C sec_add = ENC_OK \<and>
	                  enc_sections_state_rel u data inst addr sec_add
	                    ?add_state \<and>
	                  heap_bytes_word u pending 0 pend_len =
	                    heap_bytes_word t pending 0 pend_len \<and>
	                  heap_typing u = heap_typing t \<rbrace>"
	          apply (rule runs_to_bind_exception)
	           apply (rule runs_to_liftE)
	           apply (rule runs_to_weaken[OF add])
	          by auto
	        show ?thesis
	          unfolding flush_pending_outer_run_branch_def
	          using add_lt
	          apply simp
	          apply (rule runs_to_bind_exception)
	           apply (rule runs_to_weaken[OF add_checked])
	           apply clarsimp
	           subgoal premises add_post for u sec_add
	           proof -
	             have rel_add:
	               "enc_sections_state_rel u data inst addr sec_add ?add_state"
	               using add_post by auto
	             have sec_add_ok:
	               "sections_t_C.err_C sec_add = ENC_OK"
	               using add_post by auto
	             have typing_u_s0: "heap_typing u = heap_typing s"
	               using add_post typing_t_s0 by auto
	             have frame_u_s:
	               "heap_bytes_word u pending 0 pend_len =
	                heap_bytes_word s pending 0 pend_len"
	               using add_post frame_t by auto
	             have typing_u_s: "heap_typing u = heap_typing s"
	               using add_post typing_t_s by auto
	             have run:
	               "emit_run' sec_add data data_cap inst inst_cap b (j - i) \<bullet> u
	                \<lbrace> \<lambda>r v.
	                     (\<exists>sec'.
	                       r = Result sec' \<and>
	                       sections_t_C.err_C sec' = ENC_OK \<and>
	                       enc_sections_state_rel v data inst addr sec'
	                         ?run_state) \<and>
	                     heap_bytes_word v pending 0 pend_len =
	                       heap_bytes_word u pending 0 pend_len \<and>
	                     heap_typing v = heap_typing u \<rbrace>"
	               apply (rule runs_to_weaken)
	                apply (rule emit_pending_run_chunk_from_loop_buffers[
	                  where spec_src_len = "sl"
	                    and spec_st =
	                      "emit_inst_spec (sl)
	                        (RAdd (heap_bytes_word s pending add_start
	                          (i - add_start))) loop_st"
	                    and pending_frame_off = 0
	                    and pending_frame_len = pend_len])
                         apply (rule buffers)
	                        apply (rule typing_u_s0)
	                       apply (rule rel_add)
	                      apply (rule sec_add_ok)
	                     apply (simp add: pend_len_le)
	                    apply (rule add_run_data_room[OF rel_add])
	                   apply (rule add_run_inst_room[OF rel_add])
	                  apply (rule add_run_addr_room[OF rel_add])
	               using add_state_eq_base add_lt
	               apply (auto simp: flush_pending_outer_run_state_def)
	               done
	             have run_checked:
	               "(do {
	                   sec_run \<leftarrow> liftE
	                     (emit_run' sec_add data data_cap inst inst_cap b
	                       (j - i));
	                   unless (sections_t_C.err_C sec_run = ENC_OK)
	                     (throw sec_run);
	                   return (j, j, sec_run)
	                 }) \<bullet> u
	                \<lbrace> \<lambda>r v.
	                     \<exists>sec'.
	                       r = Result (j, j, sec') \<and>
	                       sections_t_C.err_C sec' = ENC_OK \<and>
	                       heap_bytes_word v pending 0 pend_len =
	                         heap_bytes_word s pending 0 pend_len \<and>
	                       heap_typing v = heap_typing s \<and>
	                       enc_sections_state_rel v data inst addr sec'
	                         ?run_state \<rbrace>"
	               apply (rule runs_to_bind_exception)
	                apply (rule runs_to_liftE)
	                apply (rule runs_to_weaken[OF run])
	               using frame_u_s typing_u_s
	               by auto
	             show ?thesis
	               by (rule run_checked)
	           qed
	          done
	      qed
    qed
    have flush:
      "flush_pending' sec data data_cap inst inst_cap pending pend_len \<bullet> s
       \<lbrace> \<lambda>r t. \<exists>sec'.
            r = Result sec' \<and>
            enc_sections_state_rel t data inst addr sec'
              (flush_pending_spec sl spec_st) \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            heap_typing t = heap_typing s \<rbrace>"
      apply (rule runs_to_weaken[
       OF flush_pending'_enc_sections_state_rel_branch_pre[
         where src_len = "sl",
         OF rel pending_eq sec_ok pending_valid run_pre tail_pre]])
      apply auto
      done
  show ?thesis by (rule flush)
qed



lemma encode_window_try_fused_copy_step_topdown_budget:
  assumes rel:
    "encode_window_loop_budget_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and tp_lt: "tp < tgt_len"
      and match:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
      and match_len: "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
      and fused:
    "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st =
      Some spec_st'"
  shows "encode_window_c_match_branch src_len
            data data_cap inst inst_cap addr addr_cap pending pend_len
            sec tp m \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st''.
              r = Result (pend_len', sec', tp') \<and>
              encode_window_loop_budget_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st'' \<and>
              enc_tp spec_st < enc_tp spec_st'' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp) \<rbrace>"
  sorry

lemma encode_window_flush_then_copy_step_topdown_budget:
  assumes rel:
    "encode_window_loop_budget_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and tp_lt: "tp < tgt_len"
      and match:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
      and match_len: "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
      and fused_none:
    "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st =
      None"
  shows "encode_window_c_match_branch src_len
            data data_cap inst inst_cap addr addr_cap pending pend_len
            sec tp m \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
              r = Result (pend_len', sec', tp') \<and>
              encode_window_loop_budget_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
              enc_tp spec_st < enc_tp spec_st' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp) \<rbrace>"
  sorry

lemma encode_window_match_step_topdown_budget:
  assumes rel:
    "encode_window_loop_budget_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
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
              encode_window_loop_budget_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
              enc_tp spec_st < enc_tp spec_st' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp) \<rbrace>"
proof -
  have find_run:
    "gets_the (find_best_match' src src_len tgt tgt_len tp head_arr next_arr)
      \<bullet> s \<lbrace> \<lambda>r t. t = s \<and> r = Result m \<rbrace>"
    unfolding gets_the_def
    apply runs_to_vcg
    using match by simp
  have match_not_short:
    "\<not> match_t_C.len_C m < (of_nat min_match :: 32 word)"
    using match_len
    by simp
  show ?thesis
  proof (cases "try_emit_add_copy_spec (length src_bytes)
      (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m)) spec_st")
    case None
    show ?thesis
      unfolding encode_window_c_loop_body_def
      apply simp
      apply (rule runs_to_bind)
       apply (rule runs_to_weaken[OF find_run])
      apply clarsimp
      using match_not_short
      apply (simp add: min_match_def)
      apply (fold encode_window_c_match_branch_def)
      apply (rule runs_to_weaken[
        OF encode_window_flush_then_copy_step_topdown_budget[
          OF rel buffers match_rel src_tgt_bound tp_lt match match_len None]])
      apply clarsimp
      done
  next
    case (Some fused)
    show ?thesis
      unfolding encode_window_c_loop_body_def
      apply simp
      apply (rule runs_to_bind)
       apply (rule runs_to_weaken[OF find_run])
      apply clarsimp
      using match_not_short
      apply (simp add: min_match_def)
      apply (fold encode_window_c_match_branch_def)
      apply (rule runs_to_weaken[
        OF encode_window_try_fused_copy_step_topdown_budget[
          OF rel buffers match_rel src_tgt_bound tp_lt match match_len Some]])
      apply clarsimp
      done
  qed
qed

lemma encode_window_loop_body_topdown_budget:
  assumes rel:
    "encode_window_loop_budget_rel s src src_len tgt tgt_len
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      sec tp pend_len src_bytes tgt_bytes spec_st"
      and match_rel:
    "encode_window_match_rel s src src_len tgt tgt_len head_arr next_arr
      src_bytes tgt_bytes"
      and buffers:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and pend_lt: "pend_len < pending_cap"
      and tp_lt: "tp < tgt_len"
      and match_result:
    "\<exists>m. find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some m"
  shows "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            (pend_len, sec, tp) \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
              r = Result (pend_len', sec', tp') \<and>
              encode_window_loop_budget_rel t src src_len tgt tgt_len
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
          encode_window_loop_budget_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
          (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp) \<rbrace>"
    by (rule encode_window_pending_byte_step_topdown_budget[
        OF rel buffers match_rel pend_lt tp_lt])
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
          encode_window_loop_budget_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
          enc_tp spec_st < enc_tp spec_st' \<and>
          (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp) \<rbrace>"
    by (rule encode_window_match_step_topdown_budget[
        OF rel buffers match_rel src_tgt_bound tp_lt])
  show ?thesis
  proof -
    obtain m where m_result:
      "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
        Some m"
      using match_result by blast
    show ?thesis
    proof (cases "match_t_C.len_C m < (of_nat min_match :: 32 word)")
      case True
      show ?thesis
      proof (rule runs_to_weaken[OF pending_case[OF True m_result]])
        fix r t
        assume post:
          "\<exists>sec' tp' pend_len' spec_st'.
            r = Result (pend_len', sec', tp') \<and>
            spec_st' = buffer_pending_byte_spec (tgt_bytes ! unat tp)
              spec_st \<and>
            encode_window_loop_budget_rel t src src_len tgt tgt_len
              data data_cap inst inst_cap addr addr_cap pending pending_cap
              sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
            (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
              measure
                (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                   unat tgt_len - unat tp)"
        then obtain sec' tp' pend_len' spec_st' where
          r_eq: "r = Result (pend_len', sec', tp')"
          and spec_eq:
            "spec_st' = buffer_pending_byte_spec (tgt_bytes ! unat tp)
              spec_st"
          and rel':
            "encode_window_loop_budget_rel t src src_len tgt tgt_len
              data data_cap inst inst_cap addr addr_cap pending pending_cap
              sec' tp' pend_len' src_bytes tgt_bytes spec_st'"
          and meas:
            "(((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
              measure
                (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                   unat tgt_len - unat tp)"
          by blast
        have progress: "enc_tp spec_st < enc_tp spec_st'"
          using spec_eq by (simp add: buffer_pending_byte_spec_def)
        show "\<exists>sec' tp' pend_len' spec_st'.
          r = Result (pend_len', sec', tp') \<and>
          encode_window_loop_budget_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
          enc_tp spec_st < enc_tp spec_st' \<and>
          (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp)"
          using r_eq rel' progress meas by blast
      qed
    next
      case False
      have match_len:
        "(of_nat min_match :: 32 word) \<le> match_t_C.len_C m"
        using False by simp
      show ?thesis
        by (rule match_case[OF m_result match_len])
    qed
  qed
qed

lemma encode_window_while_loop_topdown_budget:
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
      and final_caps:
    "encoder_final_section_caps_ok src_bytes tgt_bytes
      data_cap inst_cap addr_cap"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and init:
    "encode_window_loop_budget_rel s src src_len tgt tgt_len
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
              encode_window_loop_budget_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec tp pend_len src_bytes tgt_bytes spec_st \<and>
              flush_pending_spec (length src_bytes) spec_st =
                encode_window_final_spec_state src_bytes tgt_bytes \<and>
              encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
                src_bytes tgt_bytes \<rbrace>"
  sorry

lemma encode_window_final_flush_topdown_budget:
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
      and final_caps:
    "encoder_final_section_caps_ok src_bytes tgt_bytes
      data_cap inst_cap addr_cap"
      and loop_exit:
    "encode_window_loop_budget_rel s src src_len tgt tgt_len
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
              r = Exn sec' \<and>
              enc_sections_state_rel t data inst addr sec'
                (encode_window_final_spec_state src_bytes tgt_bytes) \<and>
              sections_t_C.err_C sec' = ENC_OK \<and>
              encoder_window_caps_ok sec' data_cap inst_cap addr_cap \<and>
              heap_typing t = heap_typing s \<rbrace>"
  sorry

lemma encode_window_phase_core_topdown_budget:
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
      and final_caps:
        "encoder_final_section_caps_ok src_bytes tgt_bytes
          data_cap inst_cap addr_cap"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
  shows "encode_window' src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>sec spec_st.
               r = Result sec \<and>
               spec_st = encode_window_final_spec_state src_bytes tgt_bytes \<and>
               enc_sections_state_rel t data inst addr sec spec_st \<and>
               sections_t_C.err_C sec = ENC_OK \<and>
               encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
               heap_typing t = heap_typing s \<rbrace>"
  sorry

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
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
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
                encode_window_final_spec_state src_bytes tgt_bytes \<and>
              encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
                src_bytes tgt_bytes \<rbrace>"
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
      encode_window_loop_buffers_ok s src src_len tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap;
      pend_len < pending_cap;
      tp < tgt_len;
      \<exists>m. find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
        Some m
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
    by (rule encode_window_loop_body_topdown[
        OF _ match_rel _ src_tgt_bound])
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
              r = Exn sec' \<and>
	              enc_sections_state_rel t data inst addr sec'
	                (encode_window_final_spec_state src_bytes tgt_bytes) \<and>
	              sections_t_C.err_C sec' = ENC_OK \<and>
	              encoder_window_caps_ok sec' data_cap inst_cap addr_cap \<and>
	              heap_typing t = heap_typing s \<rbrace>"
proof -
  have pending_eq:
    "enc_pending spec_st = heap_bytes_word s pending 0 pend_len"
    using loop_exit by (simp add: encode_window_loop_rel_def)
  have rel:
    "enc_sections_state_rel s data inst addr sec spec_st"
    using loop_exit by (simp add: encode_window_loop_rel_def)
  have sec_ok: "sections_t_C.err_C sec = ENC_OK"
    using loop_exit by (simp add: encode_window_loop_rel_def)
  have caps:
    "encoder_window_caps_ok sec data_cap inst_cap addr_cap"
    using loop_exit by (simp add: encode_window_loop_rel_def
        encoder_window_caps_ok_def)
  have src_heap:
    "heap_bytes s src (unat src_len) = src_bytes"
    using loop_exit by (simp add: encode_window_loop_rel_def)
  have tgt_heap:
    "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
    using loop_exit by (simp add: encode_window_loop_rel_def)
  have typing_s0:
    "heap_typing s = heap_typing s0"
    using index by (simp add: encoder_index_post_def)
  have pend_len_le:
    "unat pend_len \<le> unat pending_cap"
    using loop_exit by (simp add: encode_window_loop_rel_def)
  have pending_valid:
    "\<forall>j < unat pend_len.
      ptr_valid (heap_typing s)
        (pending +\<^sub>p uint ((0 :: 32 word) + of_nat j))"
    by (rule encoder_buffers_ok_pending_ptr_valid[
        OF buffers typing_s0 pend_len_le])
  show ?thesis
  proof (cases "0 < pend_len")
    case False
    have pend_zero: "pend_len = 0"
      using False by (simp add: word_gt_0)
    have pending_empty: "enc_pending spec_st = []"
      using pending_eq pend_zero
      by (simp add: heap_bytes_word_zero heap_bytes_def)
    have flush_eq:
      "flush_pending_spec (length src_bytes) spec_st = spec_st"
      using pending_empty
      by (simp add: flush_pending_spec_def flush_pending_insts_def
          emit_insts_spec_def append_add_inst_def
          close_pending_run_def pending_scan_init_def)
    have spec_eq:
      "spec_st = encode_window_final_spec_state src_bytes tgt_bytes"
      using final_spec flush_eq by simp
    show ?thesis
      using False rel sec_ok caps spec_eq
      by (auto simp: encoder_window_caps_ok_def)
  next
    case True
    let ?pending_bytes = "heap_bytes_word s pending 0 pend_len"
    let ?final_st = "encode_window_final_spec_state src_bytes tgt_bytes"
    have pending_bytes_len: "length ?pending_bytes = unat pend_len"
      by simp
    have pending_bytes32: "length ?pending_bytes < 2 ^ 32"
      using unat_lt2p[of pend_len] by simp
    have tp_le: "unat tp \<le> unat tgt_len"
      using loop_exit by (simp add: encode_window_loop_rel_def)
    have tp_eq: "unat tp = unat tgt_len"
      using exit tp_le by (simp add: word_less_nat_alt)
    have data_slack:
      "unat (sections_t_C.data_pos_C sec) + unat pend_len + 64 \<le>
       unat data_cap"
      using loop_exit tp_eq by (simp add: encode_window_loop_rel_def)
    have inst_slack:
      "unat (sections_t_C.inst_pos_C sec) + unat pend_len + 64 \<le>
       unat inst_cap"
      using loop_exit tp_eq by (simp add: encode_window_loop_rel_def)
    have addr_slack:
      "unat (sections_t_C.addr_pos_C sec) + unat pend_len + 64 \<le>
       unat addr_cap"
      using loop_exit tp_eq by (simp add: encode_window_loop_rel_def)
    have final_loop:
      "flush_pending_loop_spec (length src_bytes) ?pending_bytes 0 0
        spec_st = ?final_st"
      using flush_pending_loop_spec_eq_flush_pending_spec[OF pending_eq]
        final_spec by simp
    have final_data_growth:
      "length (enc_data ?final_st) \<le>
       length (enc_data spec_st) + unat pend_len"
      using flush_pending_loop_spec_growth(1)[
          OF order_refl zero_le pending_bytes32,
          of "length src_bytes" spec_st] final_loop pending_bytes_len
      by simp
    have final_inst_growth:
      "length (enc_inst ?final_st) \<le>
       length (enc_inst spec_st) + unat pend_len"
      using flush_pending_loop_spec_growth(2)[
          OF order_refl zero_le pending_bytes32,
          of "length src_bytes" spec_st] final_loop pending_bytes_len
      by simp
    have final_addr_growth:
      "length (enc_addr ?final_st) = length (enc_addr spec_st)"
      using flush_pending_loop_spec_growth(3)[
          OF order_refl zero_le pending_bytes32,
          of "length src_bytes" spec_st] final_loop pending_bytes_len
      by simp
    have final_data_room64:
      "length (enc_data ?final_st) + 64 \<le> unat data_cap"
      using final_data_growth enc_sections_state_rel_lengths(1)[OF rel]
        data_slack by linarith
    have final_inst_room64:
      "length (enc_inst ?final_st) + 64 \<le> unat inst_cap"
      using final_inst_growth enc_sections_state_rel_lengths(2)[OF rel]
        inst_slack by linarith
    have final_addr_room64:
      "length (enc_addr ?final_st) + 64 \<le> unat addr_cap"
      using final_addr_growth enc_sections_state_rel_lengths(3)[OF rel]
        addr_slack by linarith
    have tail_pre:
      "\<And>add_start i sec_cur t loop_st. \<lbrakk>
        flush_pending_outer_loop_inv (length src_bytes) s data inst addr
          pending pend_len spec_st add_start i sec_cur t;
        i \<le> pend_len;
        i = pend_len;
        enc_sections_state_rel t data inst addr sec_cur loop_st;
        flush_pending_loop_spec (length src_bytes)
          (heap_bytes_word s pending 0 pend_len) (unat add_start)
          (unat pend_len) loop_st =
        flush_pending_loop_spec (length src_bytes)
          (heap_bytes_word s pending 0 pend_len) 0 0 spec_st
      \<rbrakk> \<Longrightarrow>
        flush_pending_outer_tail data data_cap inst inst_cap pending pend_len
          add_start sec_cur \<bullet> t
        \<lbrace> \<lambda>Res sec' u.
	             enc_sections_state_rel u data inst addr sec'
	               (flush_pending_outer_tail_state (length src_bytes) s
	                 pending pend_len add_start loop_st) \<and>
	             sections_t_C.err_C sec' = ENC_OK \<and>
	             heap_typing u = heap_typing s \<rbrace>"
    proof -
      fix add_start i sec_cur t loop_st
      assume inv:
        "flush_pending_outer_loop_inv (length src_bytes) s data inst addr
          pending pend_len spec_st add_start i sec_cur t"
      assume i_eq: "i = pend_len"
      assume rel_cur: "enc_sections_state_rel t data inst addr sec_cur loop_st"
      assume eq_loop:
        "flush_pending_loop_spec (length src_bytes)
          (heap_bytes_word s pending 0 pend_len) (unat add_start)
          (unat pend_len) loop_st =
        flush_pending_loop_spec (length src_bytes)
          (heap_bytes_word s pending 0 pend_len) 0 0 spec_st"
      have add_start_le_len: "add_start \<le> pend_len"
        using inv i_eq by (simp add: flush_pending_outer_loop_inv_def)
      have typing_t_s: "heap_typing t = heap_typing s"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have typing_t_s0: "heap_typing t = heap_typing s0"
        using typing_t_s typing_s0 by simp
      have frame_t:
        "heap_bytes_word t pending 0 pend_len = ?pending_bytes"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have sec_cur_ok: "sections_t_C.err_C sec_cur = ENC_OK"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have exit_tail:
        "flush_pending_loop_spec (length src_bytes) ?pending_bytes
          (unat add_start) (unat pend_len) loop_st =
         flush_pending_outer_tail_state (length src_bytes) s pending
          pend_len add_start loop_st"
        unfolding flush_pending_outer_tail_state_def
        by (rule flush_pending_loop_spec_exit_heap_emit_word[
          OF add_start_le_len]) simp
      have tail_state_eq:
        "flush_pending_outer_tail_state (length src_bytes) s pending
          pend_len add_start loop_st = ?final_st"
        using exit_tail eq_loop final_loop by simp
      have add_start_nat_le_len: "unat add_start \<le> unat pend_len"
        using add_start_le_len by (simp add: word_le_nat_alt)
      have pend_nat_le_pending_bytes: "unat pend_len \<le> length ?pending_bytes"
        by simp
      have cur_data_le_loop:
        "length (enc_data loop_st) \<le>
         length (enc_data
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat add_start) (unat pend_len) loop_st))"
        by (rule flush_pending_loop_spec_mono(1)[
          OF add_start_nat_le_len pend_nat_le_pending_bytes])
      have cur_inst_le_loop:
        "length (enc_inst loop_st) \<le>
         length (enc_inst
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat add_start) (unat pend_len) loop_st))"
        by (rule flush_pending_loop_spec_mono(2)[
          OF add_start_nat_le_len pend_nat_le_pending_bytes])
      have cur_addr_eq_loop:
        "length (enc_addr
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat add_start) (unat pend_len) loop_st)) =
         length (enc_addr loop_st)"
        by (rule flush_pending_loop_spec_mono(3)[
          OF add_start_nat_le_len pend_nat_le_pending_bytes])
      have cur_data_le_final:
        "length (enc_data loop_st) \<le> length (enc_data ?final_st)"
        using cur_data_le_loop eq_loop final_loop by simp
      have cur_inst_le_final:
        "length (enc_inst loop_st) \<le> length (enc_inst ?final_st)"
        using cur_inst_le_loop eq_loop final_loop by simp
      have cur_addr_le_final:
        "length (enc_addr loop_st) = length (enc_addr ?final_st)"
        using cur_addr_eq_loop eq_loop final_loop by simp
      show "flush_pending_outer_tail data data_cap inst inst_cap pending
          pend_len add_start sec_cur \<bullet> t
        \<lbrace> \<lambda>Res sec' u.
	             enc_sections_state_rel u data inst addr sec'
	               (flush_pending_outer_tail_state (length src_bytes) s
	                 pending pend_len add_start loop_st) \<and>
	             sections_t_C.err_C sec' = ENC_OK \<and>
	             heap_typing u = heap_typing s \<rbrace>"
      proof (cases "add_start < pend_len")
        case False
	        show ?thesis
	          using False rel_cur typing_t_s sec_cur_ok
	          by (auto simp: flush_pending_outer_tail_def
	              flush_pending_outer_tail_state_def enc_sections_state_rel_def)
      next
        case add_lt: True
        let ?sz = "pend_len - add_start"
        let ?add_state =
          "emit_inst_spec (length src_bytes)
            (RAdd (heap_bytes_word s pending add_start ?sz)) loop_st"
        have add_pending_clear:
          "?add_state\<lparr>enc_pending := []\<rparr> = ?final_st"
          using tail_state_eq add_lt
          by (simp add: flush_pending_outer_tail_state_def)
        have add_sections_final:
          "enc_data ?add_state = enc_data ?final_st"
          "enc_inst ?add_state = enc_inst ?final_st"
          "enc_addr ?add_state = enc_addr ?final_st"
          using arg_cong[OF add_pending_clear, of enc_data]
            arg_cong[OF add_pending_clear, of enc_inst]
            arg_cong[OF add_pending_clear, of enc_addr]
          by simp_all
        have sz_ge: "(1 :: 32 word) \<le> ?sz"
          using add_lt by unat_arith
        have pending_range:
          "unat add_start + unat ?sz \<le> unat pending_cap"
          using add_start_le_len pend_len_le by unat_arith
        have slice_eq:
          "heap_bytes_word t pending add_start ?sz =
           heap_bytes_word s pending add_start ?sz"
          by (rule heap_bytes_word_slice_eq_from_zero_frame[
            OF frame_t]) (use add_start_le_len in unat_arith)
        have data_room_add:
          "unat (sections_t_C.data_pos_C sec_cur) + unat ?sz \<le>
           unat data_cap"
        proof -
          have add_len:
            "length (enc_data ?add_state) =
             unat (sections_t_C.data_pos_C sec_cur) + unat ?sz"
            using enc_sections_state_rel_lengths(1)[OF rel_cur] add_lt
            by (simp add: emit_inst_spec_RAdd_sections_general)
          have "length (enc_data ?add_state) =
                length (enc_data ?final_st)"
            using add_sections_final(1) by simp
          then show ?thesis
            using add_len final_data_room64 by linarith
        qed
        have inst_room_add:
          "unat (sections_t_C.inst_pos_C sec_cur) + 6 \<le>
           unat inst_cap"
          using enc_sections_state_rel_lengths(2)[OF rel_cur]
            cur_inst_le_final final_inst_room64 by linarith
        have addr_room_add:
          "unat (sections_t_C.addr_pos_C sec_cur) \<le> unat addr_cap"
          using enc_sections_state_rel_lengths(3)[OF rel_cur]
            cur_addr_le_final final_addr_room64 by linarith
        have add:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?add_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t \<rbrace>"
          apply (rule runs_to_weaken)
           apply (rule emit_pending_add_chunk_from_loop_buffers[
            where spec_src_len = "length src_bytes"
              and pending_frame_off = 0
              and pending_frame_len = pend_len])
                    apply (rule encoder_buffers_ok_encode_window_loop_buffers_ok[OF buffers])
                   apply (rule typing_t_s0)
                  apply (rule rel_cur)
                 apply (rule sec_cur_ok)
                apply (rule sz_ge)
               apply (rule pending_range)
              apply (simp add: pend_len_le)
             apply (rule data_room_add)
            apply (rule inst_room_add)
           apply (rule addr_room_add)
          using slice_eq by auto
        show ?thesis
          unfolding flush_pending_outer_tail_def
          using add_lt
          apply simp
          apply (rule runs_to_weaken[OF add])
          using typing_t_s frame_t tail_state_eq add_lt add_sections_final
          apply (auto simp: flush_pending_outer_tail_state_def
              enc_sections_state_rel_def)
          done
      qed
    qed
    have run_pre:
      "\<And>add_start i sec_cur t j b loop_st. \<lbrakk>
        flush_pending_outer_loop_inv (length src_bytes) s data inst addr
          pending pend_len spec_st add_start i sec_cur t;
        i \<le> pend_len;
        i < j;
        j \<le> pend_len;
        pending_run_end (heap_bytes_word s pending 0 pend_len) (unat i) =
          unat j;
        (4 :: 32 word) \<le> j - i;
        b = heap_w8 s (pending +\<^sub>p uint i);
        enc_sections_state_rel t data inst addr sec_cur loop_st;
        flush_pending_loop_spec (length src_bytes)
          (heap_bytes_word s pending 0 pend_len) (unat add_start) (unat i)
          loop_st =
        flush_pending_loop_spec (length src_bytes)
          (heap_bytes_word s pending 0 pend_len) 0 0 spec_st
      \<rbrakk> \<Longrightarrow>
        flush_pending_outer_run_branch data data_cap inst inst_cap pending
          add_start i j b sec_cur \<bullet> t
        \<lbrace> \<lambda>r u.
             \<exists>sec'.
               r = Result (j, j, sec') \<and>
               sections_t_C.err_C sec' = ENC_OK \<and>
               heap_bytes_word u pending 0 pend_len =
                 heap_bytes_word s pending 0 pend_len \<and>
               heap_typing u = heap_typing s \<and>
               enc_sections_state_rel u data inst addr sec'
                 (flush_pending_outer_run_state (length src_bytes) s
                   pending add_start i j b loop_st) \<rbrace>"
    proof -
      fix add_start i sec_cur t j b loop_st
      assume inv:
        "flush_pending_outer_loop_inv (length src_bytes) s data inst addr
          pending pend_len spec_st add_start i sec_cur t"
      assume i_le_len: "i \<le> pend_len"
        and i_lt_j: "i < j"
        and j_le_len: "j \<le> pend_len"
        and run_end:
          "pending_run_end (heap_bytes_word s pending 0 pend_len) (unat i) =
           unat j"
        and run_ge: "(4 :: 32 word) \<le> j - i"
        and b_eq: "b = heap_w8 s (pending +\<^sub>p uint i)"
        and rel_cur: "enc_sections_state_rel t data inst addr sec_cur loop_st"
        and eq_loop:
          "flush_pending_loop_spec (length src_bytes)
            (heap_bytes_word s pending 0 pend_len) (unat add_start)
            (unat i) loop_st =
           flush_pending_loop_spec (length src_bytes)
            (heap_bytes_word s pending 0 pend_len) 0 0 spec_st"
      have add_start_le_i: "add_start \<le> i"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have typing_t_s: "heap_typing t = heap_typing s"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have typing_t_s0: "heap_typing t = heap_typing s0"
        using typing_t_s typing_s0 by simp
      have frame_t:
        "heap_bytes_word t pending 0 pend_len = ?pending_bytes"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have sec_cur_ok: "sections_t_C.err_C sec_cur = ENC_OK"
        using inv by (simp add: flush_pending_outer_loop_inv_def)
      have add_start_nat_le_i: "unat add_start \<le> unat i"
        using add_start_le_i by (simp add: word_le_nat_alt)
      have i_nat_le_pending_bytes: "unat i \<le> length ?pending_bytes"
        using i_le_len by (simp add: word_le_nat_alt)
      have j_nat_le_pending_bytes: "unat j \<le> length ?pending_bytes"
        using j_le_len by (simp add: word_le_nat_alt)
      have cur_data_le_loop:
        "length (enc_data loop_st) \<le>
         length (enc_data
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat add_start) (unat i) loop_st))"
        by (rule flush_pending_loop_spec_mono(1)[
          OF add_start_nat_le_i i_nat_le_pending_bytes])
      have cur_inst_le_loop:
        "length (enc_inst loop_st) \<le>
         length (enc_inst
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat add_start) (unat i) loop_st))"
        by (rule flush_pending_loop_spec_mono(2)[
          OF add_start_nat_le_i i_nat_le_pending_bytes])
      have cur_addr_eq_loop:
        "length (enc_addr
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat add_start) (unat i) loop_st)) =
         length (enc_addr loop_st)"
        by (rule flush_pending_loop_spec_mono(3)[
          OF add_start_nat_le_i i_nat_le_pending_bytes])
      have cur_data_le_final:
        "length (enc_data loop_st) \<le> length (enc_data ?final_st)"
        using cur_data_le_loop eq_loop final_loop by simp
      have cur_inst_le_final:
        "length (enc_inst loop_st) \<le> length (enc_inst ?final_st)"
        using cur_inst_le_loop eq_loop final_loop by simp
      have cur_addr_eq_final:
        "length (enc_addr loop_st) = length (enc_addr ?final_st)"
        using cur_addr_eq_loop eq_loop final_loop by simp
      let ?add_base =
        "if add_start < i
         then emit_inst_spec (length src_bytes)
           (RAdd (heap_bytes_word s pending add_start (i - add_start)))
           loop_st
         else loop_st"
      let ?run_state =
        "flush_pending_outer_run_state (length src_bytes) s pending
          add_start i j b loop_st"
      have step_eq:
        "flush_pending_loop_spec (length src_bytes) ?pending_bytes
          (unat add_start) (unat i) loop_st =
         flush_pending_loop_spec (length src_bytes) ?pending_bytes
          (unat j) (unat j) ?run_state"
        unfolding flush_pending_outer_run_state_def
        by (rule flush_pending_loop_spec_run_step_heap_emit_word[
          OF add_start_le_i i_lt_j j_le_len run_end run_ge b_eq])
      have run_loop_eq:
        "flush_pending_loop_spec (length src_bytes) ?pending_bytes
          (unat j) (unat j) ?run_state = ?final_st"
        using step_eq eq_loop final_loop by simp
      have run_state_data_le_loop:
        "length (enc_data ?run_state) \<le>
         length (enc_data
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat j) (unat j) ?run_state))"
        by (rule flush_pending_loop_spec_mono(1)[
          OF order_refl j_nat_le_pending_bytes])
      have run_state_inst_le_loop:
        "length (enc_inst ?run_state) \<le>
         length (enc_inst
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat j) (unat j) ?run_state))"
        by (rule flush_pending_loop_spec_mono(2)[
          OF order_refl j_nat_le_pending_bytes])
      have run_state_addr_eq_loop:
        "length (enc_addr
          (flush_pending_loop_spec (length src_bytes) ?pending_bytes
            (unat j) (unat j) ?run_state)) =
         length (enc_addr ?run_state)"
        by (rule flush_pending_loop_spec_mono(3)[
          OF order_refl j_nat_le_pending_bytes])
      have run_state_data_le_final:
        "length (enc_data ?run_state) \<le> length (enc_data ?final_st)"
        using run_state_data_le_loop run_loop_eq by simp
      have run_state_inst_le_final:
        "length (enc_inst ?run_state) \<le> length (enc_inst ?final_st)"
        using run_state_inst_le_loop run_loop_eq by simp
      have run_state_addr_eq_final:
        "length (enc_addr ?run_state) = length (enc_addr ?final_st)"
        using run_state_addr_eq_loop run_loop_eq by simp
      have run_len_ge_nat: "4 \<le> unat (j - i)"
        using run_ge by (simp add: word_le_nat_alt)
      have add_base_data_plus:
        "length (enc_data ?run_state) = length (enc_data ?add_base) + 1"
        unfolding flush_pending_outer_run_state_def
        using run_len_ge_nat
        by (simp add: emit_inst_spec_RRun_sections_general)
      show "flush_pending_outer_run_branch data data_cap inst inst_cap pending
          add_start i j b sec_cur \<bullet> t
        \<lbrace> \<lambda>r u.
             \<exists>sec'.
               r = Result (j, j, sec') \<and>
               sections_t_C.err_C sec' = ENC_OK \<and>
               heap_bytes_word u pending 0 pend_len =
                 heap_bytes_word s pending 0 pend_len \<and>
               heap_typing u = heap_typing s \<and>
               enc_sections_state_rel u data inst addr sec'
                 ?run_state \<rbrace>"
      proof (cases "add_start < i")
        case no_add: False
        have data_room_run:
          "unat (sections_t_C.data_pos_C sec_cur) + 1 \<le> unat data_cap"
          using enc_sections_state_rel_lengths(1)[OF rel_cur]
            cur_data_le_final final_data_room64 by linarith
        have inst_room_run:
          "unat (sections_t_C.inst_pos_C sec_cur) + 6 \<le> unat inst_cap"
          using enc_sections_state_rel_lengths(2)[OF rel_cur]
            cur_inst_le_final final_inst_room64 by linarith
        have addr_room_run:
          "unat (sections_t_C.addr_pos_C sec_cur) \<le> unat addr_cap"
          using enc_sections_state_rel_lengths(3)[OF rel_cur]
            cur_addr_eq_final final_addr_room64 by linarith
        have run:
          "emit_run' sec_cur data data_cap inst inst_cap b (j - i) \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?run_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t \<rbrace>"
          unfolding flush_pending_outer_run_state_def
          using no_add
          apply simp
	          apply (rule emit_pending_run_chunk_from_loop_buffers[
	            where spec_src_len = "length src_bytes"
	              and pending_frame_off = 0
	              and pending_frame_len = pend_len])
                   apply (rule encoder_buffers_ok_encode_window_loop_buffers_ok[OF buffers])
                  apply (rule typing_t_s0)
                 apply (rule rel_cur)
                apply (rule sec_cur_ok)
               apply (simp add: pend_len_le)
              apply (rule data_room_run)
             apply (rule inst_room_run)
            apply (rule addr_room_run)
          done
        show ?thesis
          unfolding flush_pending_outer_run_branch_def
          using no_add
          apply simp
          apply (rule runs_to_bind_exception)
           apply (rule runs_to_liftE)
           apply (rule runs_to_weaken[OF run])
          using frame_t typing_t_s
          apply auto
          done
      next
        case add_lt: True
        let ?sz = "i - add_start"
        let ?add_state =
          "emit_inst_spec (length src_bytes)
            (RAdd (heap_bytes_word s pending add_start ?sz)) loop_st"
        have sz_ge: "(1 :: 32 word) \<le> ?sz"
          using add_lt by unat_arith
        have pending_range:
          "unat add_start + unat ?sz \<le> unat pending_cap"
          using add_start_le_i i_le_len pend_len_le by unat_arith
        have slice_eq:
          "heap_bytes_word t pending add_start ?sz =
           heap_bytes_word s pending add_start ?sz"
          by (rule heap_bytes_word_slice_eq_from_zero_frame[
            OF frame_t]) (use add_start_le_i i_le_len in unat_arith)
        have add_state_eq_base:
          "?add_state = ?add_base"
          using add_lt by simp
        have add_base_inst_le_run:
          "length (enc_inst ?add_base) \<le> length (enc_inst ?run_state)"
          unfolding flush_pending_outer_run_state_def
          by (simp add: emit_inst_spec_RRun_sections_general)
        have add_base_inst_len:
          "length (enc_inst ?add_base) = length (enc_inst ?add_state)"
          using add_state_eq_base by simp
        have add_state_inst_le_final:
          "length (enc_inst ?add_state) \<le> length (enc_inst ?final_st)"
          using add_base_inst_le_run add_base_inst_len
            run_state_inst_le_final by linarith
        have add_state_addr_eq_final:
          "length (enc_addr ?add_state) = length (enc_addr ?final_st)"
          using add_state_eq_base run_state_addr_eq_final
          unfolding flush_pending_outer_run_state_def
          by (simp add: emit_inst_spec_RRun_sections_general)
        have add_data_room:
          "unat (sections_t_C.data_pos_C sec_cur) + unat ?sz \<le>
           unat data_cap"
        proof -
          have add_len:
            "length (enc_data ?add_state) =
             unat (sections_t_C.data_pos_C sec_cur) + unat ?sz"
            using enc_sections_state_rel_lengths(1)[OF rel_cur] add_lt
            by (simp add: emit_inst_spec_RAdd_sections_general)
          have add_base_data_len:
            "length (enc_data ?add_base) = length (enc_data ?add_state)"
            using add_state_eq_base by simp
          have add_state_plus_le_final:
            "length (enc_data ?add_state) + 1 \<le>
             length (enc_data ?final_st)"
            using add_base_data_plus run_state_data_le_final
              add_base_data_len by linarith
          have "length (enc_data ?add_state) \<le>
                length (enc_data ?final_st)"
            using add_state_plus_le_final by linarith
          then show ?thesis
            using add_len final_data_room64 by linarith
        qed
        have add_inst_room:
          "unat (sections_t_C.inst_pos_C sec_cur) + 6 \<le>
           unat inst_cap"
          using enc_sections_state_rel_lengths(2)[OF rel_cur]
            cur_inst_le_final final_inst_room64 by linarith
        have add_addr_room:
          "unat (sections_t_C.addr_pos_C sec_cur) \<le> unat addr_cap"
          using enc_sections_state_rel_lengths(3)[OF rel_cur]
            cur_addr_eq_final final_addr_room64 by linarith
        have add:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?add_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t \<rbrace>"
          apply (rule runs_to_weaken)
           apply (rule emit_pending_add_chunk_from_loop_buffers[
            where spec_src_len = "length src_bytes"
              and pending_frame_off = 0
              and pending_frame_len = pend_len])
                    apply (rule encoder_buffers_ok_encode_window_loop_buffers_ok[OF buffers])
                   apply (rule typing_t_s0)
                  apply (rule rel_cur)
                 apply (rule sec_cur_ok)
                apply (rule sz_ge)
               apply (rule pending_range)
              apply (simp add: pend_len_le)
             apply (rule add_data_room)
            apply (rule add_inst_room)
           apply (rule add_addr_room)
          using slice_eq by auto
        have add_run_data_room:
          "\<And>u sec_add. enc_sections_state_rel u data inst addr sec_add
              ?add_state \<Longrightarrow>
            unat (sections_t_C.data_pos_C sec_add) + 1 \<le>
              unat data_cap"
          using add_base_data_plus run_state_data_le_final add_state_eq_base
            final_data_room64
          by (simp add: enc_sections_state_rel_lengths)
        have add_run_inst_room:
          "\<And>u sec_add. enc_sections_state_rel u data inst addr sec_add
              ?add_state \<Longrightarrow>
            unat (sections_t_C.inst_pos_C sec_add) + 6 \<le>
              unat inst_cap"
          using add_state_inst_le_final final_inst_room64
          by (simp add: enc_sections_state_rel_lengths; linarith)
	        have add_run_addr_room:
	          "\<And>u sec_add. enc_sections_state_rel u data inst addr sec_add
	              ?add_state \<Longrightarrow>
	            unat (sections_t_C.addr_pos_C sec_add) \<le> unat addr_cap"
	          using final_addr_room64 add_state_addr_eq_final
	          by (simp add: enc_sections_state_rel_lengths; linarith)
	        have add_checked:
	          "(do {
	              sec_add \<leftarrow> liftE
	                (emit_add' sec_cur data data_cap inst inst_cap pending
	                  add_start ?sz);
	              unless (sections_t_C.err_C sec_add = ENC_OK)
	                (throw sec_add);
	              return sec_add
	            }) \<bullet> t
	           \<lbrace> \<lambda>r u.
	                \<exists>sec_add.
	                  r = Result sec_add \<and>
	                  sections_t_C.err_C sec_add = ENC_OK \<and>
	                  enc_sections_state_rel u data inst addr sec_add
	                    ?add_state \<and>
	                  heap_bytes_word u pending 0 pend_len =
	                    heap_bytes_word t pending 0 pend_len \<and>
	                  heap_typing u = heap_typing t \<rbrace>"
	          apply (rule runs_to_bind_exception)
	           apply (rule runs_to_liftE)
	           apply (rule runs_to_weaken[OF add])
	          by auto
	        show ?thesis
	          unfolding flush_pending_outer_run_branch_def
	          using add_lt
	          apply simp
	          apply (rule runs_to_bind_exception)
	           apply (rule runs_to_weaken[OF add_checked])
	           apply clarsimp
	           subgoal premises add_post for u sec_add
	           proof -
	             have rel_add:
	               "enc_sections_state_rel u data inst addr sec_add ?add_state"
	               using add_post by auto
	             have sec_add_ok:
	               "sections_t_C.err_C sec_add = ENC_OK"
	               using add_post by auto
	             have typing_u_s0: "heap_typing u = heap_typing s0"
	               using add_post typing_t_s0 by auto
	             have frame_u_s:
	               "heap_bytes_word u pending 0 pend_len =
	                heap_bytes_word s pending 0 pend_len"
	               using add_post frame_t by auto
	             have typing_u_s: "heap_typing u = heap_typing s"
	               using add_post typing_t_s by auto
	             have run:
	               "emit_run' sec_add data data_cap inst inst_cap b (j - i) \<bullet> u
	                \<lbrace> \<lambda>r v.
	                     (\<exists>sec'.
	                       r = Result sec' \<and>
	                       sections_t_C.err_C sec' = ENC_OK \<and>
	                       enc_sections_state_rel v data inst addr sec'
	                         ?run_state) \<and>
	                     heap_bytes_word v pending 0 pend_len =
	                       heap_bytes_word u pending 0 pend_len \<and>
	                     heap_typing v = heap_typing u \<rbrace>"
	               apply (rule runs_to_weaken)
	                apply (rule emit_pending_run_chunk_from_loop_buffers[
	                  where spec_src_len = "length src_bytes"
	                    and spec_st =
	                      "emit_inst_spec (length src_bytes)
	                        (RAdd (heap_bytes_word s pending add_start
	                          (i - add_start))) loop_st"
	                    and pending_frame_off = 0
	                    and pending_frame_len = pend_len])
                         apply (rule encoder_buffers_ok_encode_window_loop_buffers_ok[OF buffers])
	                        apply (rule typing_u_s0)
	                       apply (rule rel_add)
	                      apply (rule sec_add_ok)
	                     apply (simp add: pend_len_le)
	                    apply (rule add_run_data_room[OF rel_add])
	                   apply (rule add_run_inst_room[OF rel_add])
	                  apply (rule add_run_addr_room[OF rel_add])
	               using add_state_eq_base add_lt
	               apply (auto simp: flush_pending_outer_run_state_def)
	               done
	             have run_checked:
	               "(do {
	                   sec_run \<leftarrow> liftE
	                     (emit_run' sec_add data data_cap inst inst_cap b
	                       (j - i));
	                   unless (sections_t_C.err_C sec_run = ENC_OK)
	                     (throw sec_run);
	                   return (j, j, sec_run)
	                 }) \<bullet> u
	                \<lbrace> \<lambda>r v.
	                     \<exists>sec'.
	                       r = Result (j, j, sec') \<and>
	                       sections_t_C.err_C sec' = ENC_OK \<and>
	                       heap_bytes_word v pending 0 pend_len =
	                         heap_bytes_word s pending 0 pend_len \<and>
	                       heap_typing v = heap_typing s \<and>
	                       enc_sections_state_rel v data inst addr sec'
	                         ?run_state \<rbrace>"
	               apply (rule runs_to_bind_exception)
	                apply (rule runs_to_liftE)
	                apply (rule runs_to_weaken[OF run])
	               using frame_u_s typing_u_s
	               by auto
	             show ?thesis
	               by (rule run_checked)
	           qed
	          done
	      qed
    qed
	    have flush:
	      "flush_pending' sec data data_cap inst inst_cap pending pend_len \<bullet> s
	       \<lbrace> \<lambda>r t. \<exists>sec'.
	            r = Result sec' \<and>
	            enc_sections_state_rel t data inst addr sec'
	              (encode_window_final_spec_state src_bytes tgt_bytes) \<and>
	            sections_t_C.err_C sec' = ENC_OK \<and>
	            heap_typing t = heap_typing s \<rbrace>"
	      apply (rule runs_to_weaken[
	       OF flush_pending'_enc_sections_state_rel_branch_pre[
	         where src_len = "length src_bytes",
	         OF rel pending_eq sec_ok pending_valid run_pre tail_pre]])
	      using final_spec
	      apply auto
	      done
	    have cond_flush:
	      "condition (\<lambda>s. 0 < pend_len)
	         (flush_pending' sec data data_cap inst inst_cap pending pend_len)
	         (return sec) \<bullet> s
	       \<lbrace> \<lambda>Res sec' t.
	            enc_sections_state_rel t data inst addr sec'
	              (encode_window_final_spec_state src_bytes tgt_bytes) \<and>
	            sections_t_C.err_C sec' = ENC_OK \<and>
	            heap_typing t = heap_typing s \<rbrace>"
	      unfolding condition_def
	      using True
	      apply runs_to_vcg
	      apply (rule runs_to_weaken[OF flush])
	      apply auto
	      done
	    show ?thesis
	      apply (rule runs_to_weaken[
	        OF runs_to_liftE_bind_throw_exn_result[OF cond_flush]])
	      subgoal premises post for r t
	      proof -
	        obtain sec' where
	            r_def: "r = Exn sec'"
	          and rel_sec:
	            "enc_sections_state_rel t data inst addr sec'
	              (encode_window_final_spec_state src_bytes tgt_bytes)"
	          and sec'_ok: "sections_t_C.err_C sec' = ENC_OK"
	          and typing_t: "heap_typing t = heap_typing s"
	          using post by auto
	        have rel_e:
	          "enc_sections_state_rel t data inst addr sec'
	            (encode_window_final_spec_state src_bytes tgt_bytes)"
	          using rel_sec .
	        have caps_e:
	          "encoder_window_caps_ok sec' data_cap inst_cap addr_cap"
	          using enc_sections_state_rel_lengths[OF rel_e]
	            final_data_room64 final_inst_room64 final_addr_room64
	          by (auto simp: encoder_window_caps_ok_def)
	        show ?thesis
	          using r_def rel_sec sec'_ok caps_e typing_t by auto
	      qed
	      done
  qed
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
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
  shows "encode_window' src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>sec spec_st.
               r = Result sec \<and>
	               spec_st = encode_window_final_spec_state src_bytes tgt_bytes \<and>
	               enc_sections_state_rel t data inst addr sec spec_st \<and>
	               sections_t_C.err_C sec = ENC_OK \<and>
	               encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
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
  have src_heap_s:
    "heap_bytes s src (unat src_len) = src_bytes"
    using index by (simp add: encoder_index_post_def)
  have tgt_heap_s:
    "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
    using index by (simp add: encoder_index_post_def)
  have typing_s:
    "heap_typing s = heap_typing s0"
    using index by (simp add: encoder_index_post_def)
  have input_lens:
    "length src_bytes = unat src_len"
    "length tgt_bytes = unat tgt_len"
    using input by (simp_all add: encoder_input_rel_def)
  let ?sec0 = "sections_t_C 0 0 0 ENC_OK"
  have reset_src:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           enc_cache_abs t cache_init \<and>
           enc_cache_wf cache_init \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t src (unat src_len) = heap_bytes s src (unat src_len) \<rbrace>"
    by (rule cache_reset'_enc_cache_abs)
  have reset_tgt:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           enc_cache_abs t cache_init \<and>
           enc_cache_wf cache_init \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len) \<rbrace>"
    by (rule cache_reset'_enc_cache_abs)
  have reset_bytes:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           enc_cache_abs t cache_init \<and>
           enc_cache_wf cache_init \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t src (unat src_len) = heap_bytes s src (unat src_len) \<and>
           heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len) \<rbrace>"
    using reset_src reset_tgt
    by (simp add: runs_to_conj)
  have reset_index:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
          encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
            src_bytes tgt_bytes \<rbrace>"
    by (rule cache_reset'_preserves_encoder_index_post[OF index])
  have reset:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           enc_cache_abs t cache_init \<and>
           enc_cache_wf cache_init \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t src (unat src_len) = heap_bytes s src (unat src_len) \<and>
           heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len) \<and>
           encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
             src_bytes tgt_bytes \<rbrace>"
    using reset_bytes reset_index
    by (simp add: runs_to_conj)
  show ?thesis
    unfolding encode_window'_def
    apply (simp add: Let_def)
    apply (rule runs_to_bind)
     apply (rule runs_to_weaken[OF reset])
    apply clarsimp
    subgoal premises reset_post for s_reset
    proof -
      have typing_reset:
        "heap_typing s_reset = heap_typing s0"
        using reset_post typing_s by simp
      have buffers_reset:
        "encoder_buffers_ok s_reset out out_cap src src_len tgt tgt_len
          head_arr next_arr pending pending_cap data data_cap inst inst_cap
          addr addr_cap"
        by (rule encoder_buffers_ok_heap_typing_eq[
            OF typing_reset buffers])
      have loop_buffers_reset:
        "encode_window_loop_buffers_ok s_reset src src_len tgt tgt_len
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
        by (rule encoder_buffers_ok_encode_window_loop_buffers_ok[
            OF buffers_reset])
      have index_reset:
        "encoder_index_post s0 s_reset src src_len tgt tgt_len head_arr
          next_arr src_bytes tgt_bytes"
        using reset_post by simp
      have init_rel:
        "encode_window_loop_rel s_reset src src_len tgt tgt_len
          data data_cap inst inst_cap addr addr_cap pending pending_cap
          ?sec0 0 0 src_bytes tgt_bytes enc_full_init"
        by (rule encode_window_initial_loop_rel[
            OF input loop_buffers_reset])
           (use reset_post src_heap_s tgt_heap_s input_lens in
              \<open>simp_all add: enc_full_init_def\<close>)
      have while_run:
        "(whileLoop (\<lambda>(pend_len, sec, tp) s. tp < tgt_len)
           (encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
             data data_cap inst inst_cap addr addr_cap pending pending_cap)
           (0, ?sec0, 0) ::
          (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
           lifted_globals) exn_monad) \<bullet> s_reset
         \<lbrace> \<lambda>r t. \<exists>pend_len sec tp spec_st.
              r = Result (pend_len, sec, tp) \<and>
              \<not> tp < tgt_len \<and>
              encode_window_loop_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec tp pend_len src_bytes tgt_bytes spec_st \<and>
              flush_pending_spec (length src_bytes) spec_st =
                encode_window_final_spec_state src_bytes tgt_bytes \<and>
              encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
                src_bytes tgt_bytes \<rbrace>"
	        by (rule encode_window_while_loop_topdown[
	            OF input buffers index_reset fit src_tgt_bound init_rel])
      show ?thesis
        apply (rule runs_to_finally)
        apply (rule runs_to_bind_exception[split_tuple g arity: 3])
         apply (rule runs_to_weaken[
           OF while_run[
             unfolded encode_window_c_loop_body_def,
             simplified Spec_Monad.return_bind]])
         apply clarsimp
        apply (rule runs_to_weaken[
          OF encode_window_final_flush_topdown[
            OF input buffers _ fit _ _ _]])
        using typing_s
        by (auto simp: encoder_index_post_def)
    qed
    done
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
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
  shows "encode_window' src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>sec.
	               r = Result sec \<and>
	               encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
	               encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
	               heap_typing t = heap_typing s \<rbrace>"
proof (rule runs_to_weaken[
    OF encode_window_phase_core_topdown[
      OF input buffers index fit src_tgt_bound]])
  fix r t
  assume post:
    "\<exists>sec spec_st.
      r = Result sec \<and>
      spec_st = encode_window_final_spec_state src_bytes tgt_bytes \<and>
	      enc_sections_state_rel t data inst addr sec spec_st \<and>
	      sections_t_C.err_C sec = ENC_OK \<and>
	      encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
	      heap_typing t = heap_typing s"
  then obtain sec spec_st where
      r_def: "r = Result sec"
    and spec_st:
      "spec_st = encode_window_final_spec_state src_bytes tgt_bytes"
	    and rel: "enc_sections_state_rel t data inst addr sec spec_st"
	    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
	    and caps: "encoder_window_caps_ok sec data_cap inst_cap addr_cap"
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
	      heap_typing t = heap_typing s"
	    using r_def fit sec_ok emitted caps typing
	    by (auto simp: encoder_window_post_def)
qed

lemma vcdiff_encode'_encode_window_phase_topdown_budget:
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
      and final_caps:
        "encoder_final_section_caps_ok src_bytes tgt_bytes
          data_cap inst_cap addr_cap"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
  shows "encode_window' src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>sec.
               r = Result sec \<and>
               encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
               encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
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
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
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
	         heap_typing t = heap_typing s_index \<rbrace>"
      by (rule vcdiff_encode'_encode_window_phase_topdown[
          OF input buffers index fit src_tgt_bound])
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

theorem vcdiff_encode'_writes_encode_spec_topdown_budget:
  fixes out src tgt pending data inst addr :: "8 word ptr"
    and out_cap src_len tgt_len pending_cap data_cap inst_cap addr_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
        "encoder_input_rel s src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr next_arr
          pending pending_cap data data_cap inst inst_cap addr addr_cap"
      and final_caps:
        "encoder_final_section_caps_ok src_bytes tgt_bytes
          data_cap inst_cap addr_cap"
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
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and out_cap_ok:
        "length (encode_spec src_bytes tgt_bytes) \<le> unat out_cap"
      and encoded_len_word:
        "length (encode_spec src_bytes tgt_bytes) < 2 ^ 32"
  shows "vcdiff_encode' out out_cap src src_len tgt tgt_len head_arr next_arr
            pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>n.
               r = Result n \<and>
               encoder_success_post out src_bytes tgt_bytes n s t \<rbrace>"
  sorry

end

end
