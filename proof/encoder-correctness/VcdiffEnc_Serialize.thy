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

lemma encode_window_pending_byte_step_topdown:
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

text \<open>Helper A: when the fused spec step is None, the C try_emit_add_copy'
  is a pure noop returning fused=0 and the original sections struct.\<close>

lemma try_emit_add_copy'_spec_none_noop:
  fixes copy_addr here copy_len pend_len :: "32 word"
  assumes rel: "enc_sections_state_rel s data inst addr_buf sec spec_st"
      and pend_eq: "length (enc_pending spec_st) = unat pend_len"
      and copy_ge: "(4 :: 32 word) \<le> copy_len"
      and none:
        "try_emit_add_copy_spec sl (unat copy_addr) (unat copy_len) spec_st
          = None"
      and bm: "best_mode' copy_addr here s = Some bm_m"
      and mode_le8: "mode_t_C.mode_C bm_m \<le> (8 :: 32 word)"
      and addr_exact:
        "encode_address (enc_cache spec_st) (unat copy_addr)
           (sl + enc_tp spec_st) =
         (unat (mode_t_C.mode_C bm_m), addr_bytes,
          cache_update (enc_cache spec_st) (unat copy_addr))"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
         \<lbrace> \<lambda>r t.
              (\<exists>f. r = Result f \<and>
                   fused_t_C.s_C f = sec \<and>
                   fused_t_C.fused_C f = 0) \<and>
              t = s \<rbrace>"
proof (cases "pend_len < (1 :: 32 word) \<or> (4 :: 32 word) < pend_len
              \<or> copy_len < (4 :: 32 word)")
  case True
  show ?thesis
    by (rule try_emit_add_copy'_early_noop[OF True])
next
  case False
  have pend_ne: "pend_len \<noteq> 0"
    and pend_le: "pend_len \<le> (4 :: 32 word)"
    using False by (auto simp: not_less)
  have pend_ge: "(1 :: 32 word) \<le> pend_len"
    using pend_ne by unat_arith
  have mode_gt: "(5 :: 32 word) < mode_t_C.mode_C bm_m"
  proof (rule ccontr)
    assume "\<not> (5 :: 32 word) < mode_t_C.mode_C bm_m"
    hence mode_le: "mode_t_C.mode_C bm_m \<le> (5 :: 32 word)"
      by simp
    have "try_emit_add_copy_spec sl (unat copy_addr) (unat copy_len) spec_st
            \<noteq> None"
      using try_emit_add_copy_spec_mode_le5_success[
            OF pend_eq pend_ge pend_le copy_ge mode_le addr_exact]
      by simp
    thus False using none by simp
  qed
  have copy_ne: "copy_len \<noteq> (4 :: 32 word)"
  proof (rule ccontr)
    assume "\<not> copy_len \<noteq> (4 :: 32 word)"
    hence copy_eq: "copy_len = (4 :: 32 word)" by simp
    have "try_emit_add_copy_spec sl (unat copy_addr) (unat copy_len) spec_st
            \<noteq> None"
      using try_emit_add_copy_spec_mode_gt5_success[
            OF pend_eq pend_ge pend_le copy_eq mode_gt mode_le8 addr_exact]
      by simp
    thus False using none by simp
  qed
  show ?thesis
    by (rule try_emit_add_copy'_mode_gt5_copy_ne4_noop[OF bm mode_gt copy_ne])
qed

text \<open>Keystone: a plain emit_copy' in the encode-window loop context,
  producing the exact emit_copy_spec section relation plus the cache and
  src/tgt frame needed to re-establish the budget invariant.  Uses EXACT
  section room (the budget provides no addr headroom).\<close>

lemma emit_copy'_state_rel_cache_frame_from_loop:
  fixes src tgt data inst addr pending :: "8 word ptr"
    and src_len_w tgt_len data_cap inst_cap addr_cap pending_cap :: "32 word"
    and copy_addr here copy_len :: "32 word"
    and src_len :: nat
  assumes buffers:
      "encode_window_loop_buffers_ok s src src_len_w tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and abs: "enc_cache_abs s (enc_cache spec_st)"
    and wf: "enc_cache_wf (enc_cache spec_st)"
    and bm: "best_mode' copy_addr here s = Some bm_m"
    and addr_exact:
      "encode_address (enc_cache spec_st) (unat copy_addr)
         (src_len + enc_flushed spec_st) =
       (unat (mode_t_C.mode_C bm_m),
        enc_best_bytes (mode_t_C.mode_C bm_m) (mode_t_C.arg_C bm_m),
        cache_update (enc_cache spec_st) (unat copy_addr))"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and data_pos_le: "unat (sections_t_C.data_pos_C sec) \<le> unat data_cap"
    and inst_room_spec:
      "length (enc_inst (emit_copy_spec src_len (unat copy_addr)
         (unat copy_len) spec_st)) \<le> unat inst_cap"
    and addr_room_spec:
      "length (enc_addr (emit_copy_spec src_len (unat copy_addr)
         (unat copy_len) spec_st)) \<le> unat addr_cap"
  shows "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec'.
              r = Result sec' \<and>
              sections_t_C.err_C sec' = ENC_OK \<and>
              sections_t_C.data_pos_C sec' = sections_t_C.data_pos_C sec \<and>
              unat (sections_t_C.inst_pos_C sec') \<le> unat inst_cap \<and>
              unat (sections_t_C.addr_pos_C sec') \<le> unat addr_cap \<and>
              enc_sections_state_rel t data inst addr sec'
                (emit_copy_spec src_len (unat copy_addr) (unat copy_len)
                  spec_st) \<and>
              enc_cache_abs t
                (cache_update (enc_cache spec_st) (unat copy_addr)) \<and>
              enc_cache_wf
                (cache_update (enc_cache spec_st) (unat copy_addr)) \<and>
              heap_bytes t src (unat src_len_w) =
                heap_bytes s src (unat src_len_w) \<and>
              heap_bytes t tgt (unat tgt_len) =
                heap_bytes s tgt (unat tgt_len) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?spec' = "emit_copy_spec src_len (unat copy_addr) (unat copy_len) spec_st"
  let ?c1 = "cache_update (enc_cache spec_st) (unat copy_addr)"
  let ?ip = "sections_t_C.inst_pos_C sec"
  let ?ap = "sections_t_C.addr_pos_C sec"
  let ?dp = "sections_t_C.data_pos_C sec"
  have src_valid: "buf_valid s src (unat src_len_w)"
    and tgt_valid: "buf_valid s tgt (unat tgt_len)"
    and data_valid: "buf_valid s data (unat data_cap)"
    and inst_valid: "buf_valid s inst (unat inst_cap)"
    and addr_valid: "buf_valid s addr (unat addr_cap)"
    and inst_dist: "ptr_range_distinct inst (unat inst_cap)"
    and addr_dist: "ptr_range_distinct addr (unat addr_cap)"
    and data_inst: "bufs_disjoint data (unat data_cap) inst (unat inst_cap)"
    and data_addr: "bufs_disjoint data (unat data_cap) addr (unat addr_cap)"
    and inst_addr: "bufs_disjoint inst (unat inst_cap) addr (unat addr_cap)"
    and inst_src: "bufs_disjoint inst (unat inst_cap) src (unat src_len_w)"
    and inst_tgt: "bufs_disjoint inst (unat inst_cap) tgt (unat tgt_len)"
    and addr_src: "bufs_disjoint addr (unat addr_cap) src (unat src_len_w)"
    and addr_tgt: "bufs_disjoint addr (unat addr_cap) tgt (unat tgt_len)"
    using buffers by (auto simp: encode_window_loop_buffers_ok_def)
  have inst_len_eq: "length (enc_inst spec_st) = unat ?ip"
    and addr_len_eq: "length (enc_addr spec_st) = unat ?ap"
    using enc_sections_state_rel_lengths[OF rel] by simp_all
  have inst_pos_le: "unat ?ip \<le> unat inst_cap"
    using inst_room_spec inst_len_eq
      emit_copy_spec_sections_mono[of spec_st src_len "unat copy_addr" "unat copy_len"]
    by simp
  have addr_pos_le: "unat ?ap \<le> unat addr_cap"
    using addr_room_spec addr_len_eq
      emit_copy_spec_sections_mono[of spec_st src_len "unat copy_addr" "unat copy_len"]
    by simp
  obtain an where addr_size: "varint_size' (mode_t_C.arg_C bm_m) s = Some an"
    using varint_size'_some by blast
  obtain sn where copy_size: "varint_size' copy_len s = Some sn"
    using varint_size'_some by blast
  have an_le5: "unat an \<le> 5" by (rule varint_size'_le5[OF addr_size])
  have sn_le5: "unat sn \<le> 5" by (rule varint_size'_le5[OF copy_size])
  have mode_le8: "mode_t_C.mode_C bm_m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[
          OF best_mode'_encode_address_correct[OF abs wf bm]])
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have addr_choice_gt5:
    "\<not> mode_t_C.mode_C bm_m < (6 :: 32 word) \<Longrightarrow>
     encode_address (enc_cache spec_st) (unat copy_addr)
       (src_len + enc_flushed spec_st) =
     (unat (mode_t_C.mode_C bm_m), [ucast (mode_t_C.arg_C bm_m)], ?c1)"
    using addr_exact by (simp add: enc_best_bytes_def)
  have addr_choice_le5:
    "mode_t_C.mode_C bm_m < (6 :: 32 word) \<Longrightarrow>
     encode_address (enc_cache spec_st) (unat copy_addr)
       (src_len + enc_flushed spec_st) =
     (unat (mode_t_C.mode_C bm_m), varint_bytes32 (mode_t_C.arg_C bm_m) an, ?c1)"
    using addr_exact varint_bytes32_eq_varint_encode[OF addr_size]
    by (simp add: enc_best_bytes_def)

  \<comment> \<open>--- conditional frame facts, proved once, instantiated per case ---\<close>
  have ibp: "unat ?ip < unat inst_cap \<Longrightarrow>
      ptr_valid (heap_typing s) (inst +\<^sub>p uint ?ip)"
    by (rule buf_valid_uintD[OF inst_valid])
  have ibd: "unat ?ip < unat inst_cap \<Longrightarrow>
      ptr_range_distinct inst (Suc (unat ?ip))"
    by (rule ptr_range_distinct_mono[OF inst_dist]) simp
  have ibdd: "unat ?ip < unat inst_cap \<Longrightarrow>
      \<forall>i < unat ?dp. data +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
  proof (intro impI allI impI)
    fix i assume IL: "unat ?ip < unat inst_cap" and i_lt: "i < unat ?dp"
    have "i < unat data_cap" using i_lt data_pos_le by linarith
    thus "data +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
      by (rule bufs_disjoint_int_uintD[OF data_inst _ IL])
  qed
  have ibad: "unat ?ip < unat inst_cap \<Longrightarrow>
      \<forall>i < unat ?ap. addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
  proof (intro impI allI impI)
    fix i assume IL: "unat ?ip < unat inst_cap" and i_lt: "i < unat ?ap"
    have i_cap: "i < unat addr_cap" using i_lt addr_pos_le by linarith
    show "addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
      by (rule bufs_disjoint_int_uintD[OF bufs_disjoint_sym[THEN iffD1, OF inst_addr] i_cap IL])
  qed
  have sib: "unat ?ip < unat inst_cap \<Longrightarrow>
      \<forall>i < unat src_len_w. src +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
  proof (intro impI allI impI)
    fix i assume H: "unat ?ip < unat inst_cap" and i_lt: "i < unat src_len_w"
    show "src +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
      by (rule bufs_disjoint_int_uintD[OF bufs_disjoint_sym[THEN iffD1, OF inst_src] i_lt H])
  qed
  have tib: "unat ?ip < unat inst_cap \<Longrightarrow>
      \<forall>i < unat tgt_len. tgt +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
  proof (intro impI allI impI)
    fix i assume H: "unat ?ip < unat inst_cap" and i_lt: "i < unat tgt_len"
    show "tgt +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
      by (rule bufs_disjoint_int_uintD[OF bufs_disjoint_sym[THEN iffD1, OF inst_tgt] i_lt H])
  qed
  have abp: "unat ?ap < unat addr_cap \<Longrightarrow>
      ptr_valid (heap_typing s) (addr +\<^sub>p uint ?ap)"
    by (rule buf_valid_uintD[OF addr_valid])
  have abd: "unat ?ap < unat addr_cap \<Longrightarrow>
      ptr_range_distinct addr (Suc (unat ?ap))"
    by (rule ptr_range_distinct_mono[OF addr_dist]) simp
  have abdd: "unat ?ap < unat addr_cap \<Longrightarrow>
      \<forall>i < unat ?dp. data +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
  proof (intro impI allI impI)
    fix i assume AL: "unat ?ap < unat addr_cap" and i_lt: "i < unat ?dp"
    have "i < unat data_cap" using i_lt data_pos_le by linarith
    thus "data +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
      by (rule bufs_disjoint_int_uintD[OF data_addr _ AL])
  qed
  have sab: "unat ?ap < unat addr_cap \<Longrightarrow>
      \<forall>i < unat src_len_w. src +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
  proof (intro impI allI impI)
    fix i assume H: "unat ?ap < unat addr_cap" and i_lt: "i < unat src_len_w"
    show "src +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
      by (rule bufs_disjoint_int_uintD[OF bufs_disjoint_sym[THEN iffD1, OF addr_src] i_lt H])
  qed
  have tab: "unat ?ap < unat addr_cap \<Longrightarrow>
      \<forall>i < unat tgt_len. tgt +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
  proof (intro impI allI impI)
    fix i assume H: "unat ?ap < unat addr_cap" and i_lt: "i < unat tgt_len"
    show "tgt +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
      by (rule bufs_disjoint_int_uintD[OF bufs_disjoint_sym[THEN iffD1, OF addr_tgt] i_lt H])
  qed
  \<comment> \<open>addr byte vs inst prefix (bound n \<le> inst_cap)\<close>
  have abid: "\<And>n. n \<le> unat inst_cap \<Longrightarrow>
      \<forall>i < n. inst +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
    if AL: "unat ?ap < unat addr_cap" for AL
  proof -
    fix n :: nat assume n_le: "n \<le> unat inst_cap"
    show "\<forall>i < n. inst +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
    proof (intro allI impI)
      fix i assume "i < n"
      hence i_cap: "i < unat inst_cap" using n_le by linarith
      show "inst +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
        by (rule bufs_disjoint_int_uintD[OF inst_addr i_cap AL])
    qed
  qed
  \<comment> \<open>addr varint facts, given addr_pos + an \<le> addr_cap\<close>
  have avf: "unat ?ap + unat an \<le> unat addr_cap \<Longrightarrow> \<not> addr_cap - ?ap < an"
    by (rule word_sub_not_less_of_unat_add_le)
  have avno: "unat ?ap + unat an \<le> unat addr_cap \<Longrightarrow>
      unat ?ap + unat an < 2 ^ 32"
    using unat_lt2p[of addr_cap] by simp
  have avv: "unat ?ap + unat an \<le> unat addr_cap \<Longrightarrow>
      \<forall>j < unat an. ptr_valid (heap_typing s) (addr +\<^sub>p uint (?ap + of_nat j))"
  proof (intro impI allI impI)
    fix j assume AN: "unat ?ap + unat an \<le> unat addr_cap" and j_lt: "j < unat an"
    show "ptr_valid (heap_typing s) (addr +\<^sub>p uint (?ap + of_nat j))"
      by (rule buf_valid_word_rangeD[OF addr_valid j_lt avno[OF AN] AN])
  qed
  have avi: "unat ?ap + unat an \<le> unat addr_cap \<Longrightarrow>
      \<forall>i < unat an. \<forall>j < unat an. i \<noteq> j \<longrightarrow>
        addr +\<^sub>p uint (?ap + of_nat i) \<noteq> addr +\<^sub>p uint (?ap + of_nat j)"
  proof (intro impI allI impI)
    fix i j assume AN: "unat ?ap + unat an \<le> unat addr_cap"
      and i_lt: "i < unat an" and j_lt: "j < unat an" and ne: "i \<noteq> j"
    show "addr +\<^sub>p uint (?ap + of_nat i) \<noteq> addr +\<^sub>p uint (?ap + of_nat j)"
    proof
      assume "addr +\<^sub>p uint (?ap + of_nat i) = addr +\<^sub>p uint (?ap + of_nat j)"
      hence "i = j"
        by (rule ptr_range_distinct_word_range_inj[OF addr_dist avno[OF AN] AN i_lt j_lt])
      thus False using ne by simp
    qed
  qed
  have avp: "unat ?ap + unat an \<le> unat addr_cap \<Longrightarrow>
      \<forall>k < unat ?ap. \<forall>i. i < an \<longrightarrow>
        addr +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
  proof (intro impI allI impI)
    fix k i assume AN: "unat ?ap + unat an \<le> unat addr_cap"
      and k_lt: "k < unat ?ap" and i_lt: "i < an"
    show "addr +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
      by (rule ptr_range_distinct_word_prefix_disj[OF addr_dist avno[OF AN] AN k_lt i_lt])
  qed
  have avdd: "unat ?ap + unat an \<le> unat addr_cap \<Longrightarrow>
      \<forall>k < unat ?dp. \<forall>i. i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
  proof (intro impI allI impI)
    fix k i assume AN: "unat ?ap + unat an \<le> unat addr_cap"
      and k_lt: "k < unat ?dp" and i_lt: "i < an"
    have "k < unat data_cap" using k_lt data_pos_le by linarith
    thus "data +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
      by (rule bufs_disjoint_word_range_rightD_word[OF data_addr _ i_lt avno[OF AN] AN])
  qed
  have sav: "unat ?ap + unat an \<le> unat addr_cap \<Longrightarrow>
      \<forall>k < unat src_len_w. \<forall>i. i < an \<longrightarrow>
        src +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
  proof (intro impI allI impI)
    fix k i assume AN: "unat ?ap + unat an \<le> unat addr_cap"
      and k_lt: "k < unat src_len_w" and i_lt: "i < an"
    show "src +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
            OF bufs_disjoint_sym[THEN iffD1, OF addr_src] k_lt i_lt avno[OF AN] AN])
  qed
  have tav: "unat ?ap + unat an \<le> unat addr_cap \<Longrightarrow>
      \<forall>k < unat tgt_len. \<forall>i. i < an \<longrightarrow>
        tgt +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
  proof (intro impI allI impI)
    fix k i assume AN: "unat ?ap + unat an \<le> unat addr_cap"
      and k_lt: "k < unat tgt_len" and i_lt: "i < an"
    show "tgt +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
            OF bufs_disjoint_sym[THEN iffD1, OF addr_tgt] k_lt i_lt avno[OF AN] AN])
  qed
  have avid: "\<And>n. \<lbrakk> unat ?ap + unat an \<le> unat addr_cap; n \<le> unat inst_cap \<rbrakk> \<Longrightarrow>
      \<forall>k < n. \<forall>i. i < an \<longrightarrow> inst +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
  proof (intro allI impI)
    fix n :: nat and k i
    assume AN: "unat ?ap + unat an \<le> unat addr_cap" and n_le: "n \<le> unat inst_cap"
      and k_lt: "k < n" and i_lt: "i < an"
    have k_cap: "k < unat inst_cap" using k_lt n_le by linarith
    show "inst +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
      by (rule bufs_disjoint_word_range_rightD_word[OF inst_addr k_cap i_lt avno[OF AN] AN])
  qed
  \<comment> \<open>inst size-varint facts, given inst_pos + 1 + sn \<le> inst_cap\<close>
  have ivf: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      \<not> inst_cap - (?ip + 1) < sn"
    by (rule word_sub_not_less_of_unat_add_le)
  have ivno: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      unat (?ip + 1) + unat sn < 2 ^ 32"
    using unat_lt2p[of inst_cap] by simp
  have ivv: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      \<forall>j < unat sn. ptr_valid (heap_typing s) (inst +\<^sub>p uint (?ip + 1 + of_nat j))"
  proof (intro impI allI impI)
    fix j assume IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap" and j_lt: "j < unat sn"
    show "ptr_valid (heap_typing s) (inst +\<^sub>p uint (?ip + 1 + of_nat j))"
      by (rule buf_valid_word_rangeD[OF inst_valid j_lt ivno[OF IN] IN])
  qed
  have ivi: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      \<forall>i < unat sn. \<forall>j < unat sn. i \<noteq> j \<longrightarrow>
        inst +\<^sub>p uint (?ip + 1 + of_nat i) \<noteq> inst +\<^sub>p uint (?ip + 1 + of_nat j)"
  proof (intro impI allI impI)
    fix i j assume IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap"
      and i_lt: "i < unat sn" and j_lt: "j < unat sn" and ne: "i \<noteq> j"
    show "inst +\<^sub>p uint (?ip + 1 + of_nat i) \<noteq> inst +\<^sub>p uint (?ip + 1 + of_nat j)"
    proof
      assume "inst +\<^sub>p uint (?ip + 1 + of_nat i) = inst +\<^sub>p uint (?ip + 1 + of_nat j)"
      hence "i = j"
        by (rule ptr_range_distinct_word_range_inj[OF inst_dist ivno[OF IN] IN i_lt j_lt])
      thus False using ne by simp
    qed
  qed
  have ivp: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      \<forall>k < unat (?ip + 1). \<forall>i. i < sn \<longrightarrow>
        inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
  proof (intro impI allI impI)
    fix k i assume IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap"
      and k_lt: "k < unat (?ip + 1)" and i_lt: "i < sn"
    show "inst +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
      by (rule ptr_range_distinct_word_prefix_disj[OF inst_dist ivno[OF IN] IN k_lt i_lt])
  qed
  have ivdd: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      \<forall>k < unat ?dp. \<forall>i. i < sn \<longrightarrow>
        data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
  proof (intro impI allI impI)
    fix k i assume IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap"
      and k_lt: "k < unat ?dp" and i_lt: "i < sn"
    have "k < unat data_cap" using k_lt data_pos_le by linarith
    thus "data +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
      by (rule bufs_disjoint_word_range_rightD_word[OF data_inst _ i_lt ivno[OF IN] IN])
  qed
  have ivad: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      \<forall>k < unat ?ap. \<forall>i. i < sn \<longrightarrow>
        addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
  proof (intro impI allI impI)
    fix k i assume IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap"
      and k_lt: "k < unat ?ap" and i_lt: "i < sn"
    have "k < unat addr_cap" using k_lt addr_pos_le by linarith
    thus "addr +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
            OF bufs_disjoint_sym[THEN iffD1, OF inst_addr] _ i_lt ivno[OF IN] IN])
  qed
  have siv: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      \<forall>k < unat src_len_w. \<forall>i. i < sn \<longrightarrow>
        src +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
  proof (intro impI allI impI)
    fix k i assume IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap"
      and k_lt: "k < unat src_len_w" and i_lt: "i < sn"
    show "src +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
            OF bufs_disjoint_sym[THEN iffD1, OF inst_src] k_lt i_lt ivno[OF IN] IN])
  qed
  have tiv: "unat (?ip + 1) + unat sn \<le> unat inst_cap \<Longrightarrow>
      \<forall>k < unat tgt_len. \<forall>i. i < sn \<longrightarrow>
        tgt +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
  proof (intro impI allI impI)
    fix k i assume IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap"
      and k_lt: "k < unat tgt_len" and i_lt: "i < sn"
    show "tgt +\<^sub>p int k \<noteq> inst +\<^sub>p uint (?ip + 1 + i)"
      by (rule bufs_disjoint_word_range_rightD_word[
            OF bufs_disjoint_sym[THEN iffD1, OF inst_tgt] k_lt i_lt ivno[OF IN] IN])
  qed
  have package:
    "\<And>ipos apos.
      emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
             enc_sections_state_rel t data inst addr sec' ?spec') \<and>
             heap_typing t = heap_typing s \<rbrace> \<Longrightarrow>
      emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and> enc_cache_abs t ?c1 \<and>
             enc_cache_wf ?c1) \<and> heap_typing t = heap_typing s \<rbrace> \<Longrightarrow>
      emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
             sections_result sec' ?dp ipos apos ENC_OK \<and>
             heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
             heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)) \<and>
             heap_typing t = heap_typing s \<rbrace> \<Longrightarrow>
      unat ipos \<le> unat inst_cap \<Longrightarrow>
      unat apos \<le> unat addr_cap \<Longrightarrow>
      emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. \<exists>sec'.
             r = Result sec' \<and>
             sections_t_C.err_C sec' = ENC_OK \<and>
             sections_t_C.data_pos_C sec' = ?dp \<and>
             unat (sections_t_C.inst_pos_C sec') \<le> unat inst_cap \<and>
             unat (sections_t_C.addr_pos_C sec') \<le> unat addr_cap \<and>
             enc_sections_state_rel t data inst addr sec' ?spec' \<and>
             enc_cache_abs t ?c1 \<and> enc_cache_wf ?c1 \<and>
             heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
             heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len) \<and>
             heap_typing t = heap_typing s \<rbrace>"
  proof -
    fix ipos apos :: "32 word"
    assume S: "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
             enc_sections_state_rel t data inst addr sec' ?spec') \<and>
             heap_typing t = heap_typing s \<rbrace>"
      and C: "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and> enc_cache_abs t ?c1 \<and>
             enc_cache_wf ?c1) \<and> heap_typing t = heap_typing s \<rbrace>"
      and F: "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
             sections_result sec' ?dp ipos apos ENC_OK \<and>
             heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
             heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)) \<and>
             heap_typing t = heap_typing s \<rbrace>"
      and Ipos: "unat ipos \<le> unat inst_cap"
      and Apos: "unat apos \<le> unat addr_cap"
    have comb: "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. ((\<exists>sec'. r = Result sec' \<and>
                   enc_sections_state_rel t data inst addr sec' ?spec') \<and>
                 heap_typing t = heap_typing s) \<and>
                ((\<exists>sec'. r = Result sec' \<and> enc_cache_abs t ?c1 \<and>
                   enc_cache_wf ?c1) \<and> heap_typing t = heap_typing s) \<and>
                ((\<exists>sec'. r = Result sec' \<and>
                   sections_result sec' ?dp ipos apos ENC_OK \<and>
                   heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
                   heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)) \<and>
                 heap_typing t = heap_typing s) \<rbrace>"
      using S C F by (simp add: runs_to_conj)
    show "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t. \<exists>sec'.
             r = Result sec' \<and>
             sections_t_C.err_C sec' = ENC_OK \<and>
             sections_t_C.data_pos_C sec' = ?dp \<and>
             unat (sections_t_C.inst_pos_C sec') \<le> unat inst_cap \<and>
             unat (sections_t_C.addr_pos_C sec') \<le> unat addr_cap \<and>
             enc_sections_state_rel t data inst addr sec' ?spec' \<and>
             enc_cache_abs t ?c1 \<and> enc_cache_wf ?c1 \<and>
             heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
             heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len) \<and>
             heap_typing t = heap_typing s \<rbrace>"
      apply (rule runs_to_weaken[OF comb])
      using Ipos Apos by (auto simp: sections_result_def)
  qed

  show ?thesis
  proof (cases "mode_t_C.mode_C bm_m < (6 :: 32 word)")
    case mode_lt: True
    note ac = addr_choice_le5[OF mode_lt]
    have abl: "length (varint_bytes32 (mode_t_C.arg_C bm_m) an) = unat an"
      using an_le5 by (simp add: varint_bytes32_def)
    show ?thesis
    proof (cases "(4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word)")
      case sz_small_c: True
      have copy_ge: "(4 :: 32 word) \<le> copy_len"
        and sz_small: "copy_len \<le> (18 :: 32 word)"
        using sz_small_c by simp_all
      have IS: "enc_inst ?spec' = enc_inst spec_st @
          [ucast (op_t_C.op_C (single_copy_opcode' copy_len (mode_t_C.mode_C bm_m)))]"
        by (rule emit_copy_spec_small_sections(2)[OF copy_ge sz_small mode_le8 ac])
      have AS: "enc_addr ?spec' = enc_addr spec_st @ varint_bytes32 (mode_t_C.arg_C bm_m) an"
        by (rule emit_copy_spec_small_sections(3)[OF copy_ge sz_small mode_le8 ac])
      have inst1_le: "unat ?ip + 1 \<le> unat inst_cap"
        using inst_room_spec IS inst_len_eq by simp
      have AN: "unat ?ap + unat an \<le> unat addr_cap"
        using addr_room_spec AS addr_len_eq abl by simp
      have IL: "unat ?ip < unat inst_cap" using inst1_le by linarith
      have ILW: "?ip < inst_cap" using IL by (simp add: word_less_nat_alt)
      have isu: "unat (?ip + 1) = unat ?ip + 1"
        using inst1_le unat_lt2p[of inst_cap] by unat_arith
      have inst1_le': "unat (?ip + 1) \<le> unat inst_cap"
        using isu inst1_le by simp
      have Apos: "unat (?ap + an) \<le> unat addr_cap"
        using AN avno[OF AN] by (simp add: unat_word_add_no_overflow)
      have srel:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec' ?spec') \<and>
                heap_typing t = heap_typing s \<rbrace>"
        by (rule runs_to_weaken[
          OF emit_copy'_small_addr_varint_success_enc_sections_state_rel[
            OF rel abs wf bm copy_ge sz_small mode_lt addr_size ac sec_ok
               ILW ibp[OF IL] ibd[OF IL] ibdd[OF IL] ibad[OF IL]
               avf[OF AN] avv[OF AN] avi[OF AN] avp[OF AN] avno[OF AN]
               avdd[OF AN] avid[OF AN inst1_le']]]) auto
      have cache:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and> enc_cache_abs t ?c1 \<and>
                enc_cache_wf ?c1) \<and> heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_small_addr_varint_success_enc_cache_abs[
            OF abs wf bm copy_ge sz_small mode_lt addr_size ILW ibp[OF IL]
               avf[OF AN] avv[OF AN]])
      have frame:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
                sections_result sec' ?dp (?ip + 1) (?ap + an) ENC_OK \<and>
                heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
                heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)) \<and>
                heap_typing t = heap_typing s \<rbrace>"
        by (rule runs_to_weaken[
          OF emit_copy'_small_addr_varint_success_heap_bytes2_frame[
            OF bm copy_ge sz_small mode_lt addr_size sec_ok near_ptr_lt
               ILW ibp[OF IL] ibd[OF IL] sib[OF IL] tib[OF IL]
               avf[OF AN] avv[OF AN] avi[OF AN] avp[OF AN] avno[OF AN]
               sav[OF AN] tav[OF AN]]]) auto
      show ?thesis
        by (rule package[OF srel cache frame inst1_le' Apos])
    next
      case sz_large: False
      hence sz_large': "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
        by simp
      have IS: "enc_inst ?spec' = enc_inst spec_st @
          [ucast (op_t_C.op_C (single_copy_opcode' copy_len (mode_t_C.mode_C bm_m)))] @
          varint_bytes32 copy_len sn"
        by (rule emit_copy_spec_large_sections(2)[OF sz_large' mode_le8 copy_size ac])
      have AS: "enc_addr ?spec' = enc_addr spec_st @ varint_bytes32 (mode_t_C.arg_C bm_m) an"
        by (rule emit_copy_spec_large_sections(3)[OF sz_large' mode_le8 copy_size ac])
      have sbl: "length (varint_bytes32 copy_len sn) = unat sn"
        using sn_le5 by (simp add: varint_bytes32_def)
      have AN: "unat ?ap + unat an \<le> unat addr_cap"
        using addr_room_spec AS addr_len_eq abl by simp
      have Apos: "unat (?ap + an) \<le> unat addr_cap"
        using AN avno[OF AN] by (simp add: unat_word_add_no_overflow)
      have inst_isn_le: "unat ?ip + 1 + unat sn \<le> unat inst_cap"
        using inst_room_spec IS inst_len_eq sbl by simp
      have IL: "unat ?ip < unat inst_cap" using inst_isn_le by linarith
      have ILW: "?ip < inst_cap" using IL by (simp add: word_less_nat_alt)
      have isu: "unat (?ip + 1) = unat ?ip + 1"
        using inst_isn_le unat_lt2p[of inst_cap] by unat_arith
      have IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap" using isu inst_isn_le by simp
      have isnu: "unat (?ip + 1 + sn) = unat (?ip + 1) + unat sn"
        using IN unat_lt2p[of inst_cap] by unat_arith
      have inst1sn_le': "unat (?ip + 1 + sn) \<le> unat inst_cap" using isnu IN by simp
      have srel:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec' ?spec') \<and>
                heap_typing t = heap_typing s \<rbrace>"
        by (rule runs_to_weaken[
          OF emit_copy'_large_addr_varint_success_enc_sections_state_rel[
            OF rel abs wf bm sz_large' copy_size mode_lt addr_size ac sec_ok
               ILW ibp[OF IL] ibd[OF IL] ibdd[OF IL] ibad[OF IL]
               ivf[OF IN] ivv[OF IN] ivi[OF IN] ivp[OF IN] ivno[OF IN]
               ivdd[OF IN] ivad[OF IN]
               avf[OF AN] avv[OF AN] avi[OF AN] avp[OF AN] avno[OF AN]
               avdd[OF AN] avid[OF AN inst1sn_le']]]) auto
      have cache:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and> enc_cache_abs t ?c1 \<and>
                enc_cache_wf ?c1) \<and> heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_large_addr_varint_success_enc_cache_abs[
            OF abs wf bm sz_large' copy_size mode_lt addr_size ILW ibp[OF IL]
               ivf[OF IN] ivv[OF IN] avf[OF AN] avv[OF AN]])
      have frame:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
                sections_result sec' ?dp (?ip + 1 + sn) (?ap + an) ENC_OK \<and>
                heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
                heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)) \<and>
                heap_typing t = heap_typing s \<rbrace>"
        by (rule runs_to_weaken[
          OF emit_copy'_large_addr_varint_success_heap_bytes2_frame[
            OF bm sz_large' copy_size mode_lt addr_size sec_ok near_ptr_lt
               ILW ibp[OF IL] ibd[OF IL] sib[OF IL] tib[OF IL]
               ivf[OF IN] ivv[OF IN] ivi[OF IN] ivp[OF IN] ivno[OF IN]
               siv[OF IN] tiv[OF IN]
               avf[OF AN] avv[OF AN] avi[OF AN] avp[OF AN] avno[OF AN]
               sav[OF AN] tav[OF AN]]]) auto
      show ?thesis
        by (rule package[OF srel cache frame inst1sn_le' Apos])
    qed
  next
    case mode_ge: False
    hence mode_ge': "\<not> mode_t_C.mode_C bm_m < (6 :: 32 word)" by simp
    note ac = addr_choice_gt5[OF mode_ge']
    show ?thesis
    proof (cases "(4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word)")
      case sz_small_c: True
      have copy_ge: "(4 :: 32 word) \<le> copy_len"
        and sz_small: "copy_len \<le> (18 :: 32 word)"
        using sz_small_c by simp_all
      have IS: "enc_inst ?spec' = enc_inst spec_st @
          [ucast (op_t_C.op_C (single_copy_opcode' copy_len (mode_t_C.mode_C bm_m)))]"
        by (rule emit_copy_spec_small_sections(2)[OF copy_ge sz_small mode_le8 ac])
      have AS: "enc_addr ?spec' = enc_addr spec_st @ [ucast (mode_t_C.arg_C bm_m)]"
        by (rule emit_copy_spec_small_sections(3)[OF copy_ge sz_small mode_le8 ac])
      have inst1_le: "unat ?ip + 1 \<le> unat inst_cap"
        using inst_room_spec IS inst_len_eq by simp
      have addr1_le: "unat ?ap + 1 \<le> unat addr_cap"
        using addr_room_spec AS addr_len_eq by simp
      have IL: "unat ?ip < unat inst_cap" using inst1_le by linarith
      have ILW: "?ip < inst_cap" using IL by (simp add: word_less_nat_alt)
      have AL: "unat ?ap < unat addr_cap" using addr1_le by linarith
      have ALW: "?ap < addr_cap" using AL by (simp add: word_less_nat_alt)
      have isu: "unat (?ip + 1) = unat ?ip + 1"
        using inst1_le unat_lt2p[of inst_cap] by unat_arith
      have inst1_le': "unat (?ip + 1) \<le> unat inst_cap" using isu inst1_le by simp
      have asu: "unat (?ap + 1) = unat ?ap + 1"
        using addr1_le unat_lt2p[of addr_cap] by unat_arith
      have addr1_le': "unat (?ap + 1) \<le> unat addr_cap" using asu addr1_le by simp
      have srel:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec' ?spec') \<and>
                heap_typing t = heap_typing s \<rbrace>"
        by (rule runs_to_weaken[
          OF emit_copy'_small_addr_byte_success_enc_sections_state_rel[
            OF rel abs wf bm copy_ge sz_small mode_ge' ac sec_ok
               ILW ibp[OF IL] ibd[OF IL] ibdd[OF IL] ibad[OF IL]
               ALW abp[OF AL] abd[OF AL] abdd[OF AL] abid[OF AL inst1_le']]]) auto
      have cache:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and> enc_cache_abs t ?c1 \<and>
                enc_cache_wf ?c1) \<and> heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_small_addr_byte_success_enc_cache_abs[
            OF abs wf bm copy_ge sz_small mode_ge' ILW ibp[OF IL] ALW abp[OF AL]])
      have frame:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
                sections_result sec' ?dp (?ip + 1) (?ap + 1) ENC_OK \<and>
                heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
                heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)) \<and>
                heap_typing t = heap_typing s \<rbrace>"
        by (rule runs_to_weaken[
          OF emit_copy'_small_addr_byte_success_heap_bytes2_frame[
            OF bm copy_ge sz_small mode_ge' sec_ok near_ptr_lt
               ILW ibp[OF IL] ibd[OF IL] sib[OF IL] tib[OF IL]
               ALW abp[OF AL] abd[OF AL] sab[OF AL] tab[OF AL]]]) auto
      show ?thesis
        by (rule package[OF srel cache frame inst1_le' addr1_le'])
    next
      case sz_large: False
      hence sz_large': "\<not> ((4 :: 32 word) \<le> copy_len \<and> copy_len \<le> (18 :: 32 word))"
        by simp
      have IS: "enc_inst ?spec' = enc_inst spec_st @
          [ucast (op_t_C.op_C (single_copy_opcode' copy_len (mode_t_C.mode_C bm_m)))] @
          varint_bytes32 copy_len sn"
        by (rule emit_copy_spec_large_sections(2)[OF sz_large' mode_le8 copy_size ac])
      have AS: "enc_addr ?spec' = enc_addr spec_st @ [ucast (mode_t_C.arg_C bm_m)]"
        by (rule emit_copy_spec_large_sections(3)[OF sz_large' mode_le8 copy_size ac])
      have sbl: "length (varint_bytes32 copy_len sn) = unat sn"
        using sn_le5 by (simp add: varint_bytes32_def)
      have addr1_le: "unat ?ap + 1 \<le> unat addr_cap"
        using addr_room_spec AS addr_len_eq by simp
      have AL: "unat ?ap < unat addr_cap" using addr1_le by linarith
      have ALW: "?ap < addr_cap" using AL by (simp add: word_less_nat_alt)
      have asu: "unat (?ap + 1) = unat ?ap + 1"
        using addr1_le unat_lt2p[of addr_cap] by unat_arith
      have addr1_le': "unat (?ap + 1) \<le> unat addr_cap" using asu addr1_le by simp
      have inst_isn_le: "unat ?ip + 1 + unat sn \<le> unat inst_cap"
        using inst_room_spec IS inst_len_eq sbl by simp
      have IL: "unat ?ip < unat inst_cap" using inst_isn_le by linarith
      have ILW: "?ip < inst_cap" using IL by (simp add: word_less_nat_alt)
      have isu: "unat (?ip + 1) = unat ?ip + 1"
        using inst_isn_le unat_lt2p[of inst_cap] by unat_arith
      have IN: "unat (?ip + 1) + unat sn \<le> unat inst_cap" using isu inst_isn_le by simp
      have isnu: "unat (?ip + 1 + sn) = unat (?ip + 1) + unat sn"
        using IN unat_lt2p[of inst_cap] by unat_arith
      have inst1sn_le': "unat (?ip + 1 + sn) \<le> unat inst_cap" using isnu IN by simp
      have srel:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
                enc_sections_state_rel t data inst addr sec' ?spec') \<and>
                heap_typing t = heap_typing s \<rbrace>"
        by (rule runs_to_weaken[
          OF emit_copy'_large_addr_byte_success_enc_sections_state_rel[
            OF rel abs wf bm sz_large' copy_size mode_ge' ac sec_ok
               ILW ibp[OF IL] ibd[OF IL] ibdd[OF IL] ibad[OF IL]
               ivf[OF IN] ivv[OF IN] ivi[OF IN] ivp[OF IN] ivno[OF IN]
               ivdd[OF IN] ivad[OF IN]
               ALW abp[OF AL] abd[OF AL] abdd[OF AL] abid[OF AL inst1sn_le']]]) auto
      have cache:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and> enc_cache_abs t ?c1 \<and>
                enc_cache_wf ?c1) \<and> heap_typing t = heap_typing s \<rbrace>"
        by (rule emit_copy'_large_addr_byte_success_enc_cache_abs[
            OF abs wf bm sz_large' copy_size mode_ge' ILW ibp[OF IL]
               ivf[OF IN] ivv[OF IN] ALW abp[OF AL]])
      have frame:
        "emit_copy' sec inst inst_cap addr addr_cap copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t. (\<exists>sec'. r = Result sec' \<and>
                sections_result sec' ?dp (?ip + 1 + sn) (?ap + 1) ENC_OK \<and>
                heap_bytes t src (unat src_len_w) = heap_bytes s src (unat src_len_w) \<and>
                heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len)) \<and>
                heap_typing t = heap_typing s \<rbrace>"
        by (rule runs_to_weaken[
          OF emit_copy'_large_addr_byte_success_heap_bytes2_frame[
            OF bm sz_large' copy_size mode_ge' sec_ok near_ptr_lt
               ILW ibp[OF IL] ibd[OF IL] sib[OF IL] tib[OF IL]
               ivf[OF IN] ivv[OF IN] ivi[OF IN] ivp[OF IN] ivno[OF IN]
               siv[OF IN] tiv[OF IN]
               ALW abp[OF AL] abd[OF AL] sab[OF AL] tab[OF AL]]]) auto
      show ?thesis
        by (rule package[OF srel cache frame inst1sn_le' addr1_le'])
    qed
  qed
qed

text \<open>Frame lemma for the mode\<le>5 fused ADD+COPY path: preserves two
  disjoint out-buffers (instantiated with src/tgt) and tracks the cache
  update, mirroring try_emit_add_copy'_mode_gt5_success_heap_bytes2_cache_frame
  with the varint address write of modes 0..5.\<close>

lemma try_emit_add_copy'_mode_le5_success_heap_bytes2_cache_frame:
  fixes csz pend_len copy_len :: "32 word"
    and m
  defines "csz \<equiv>
    (if (6 :: 32 word) < copy_len then (6 :: 32 word) else copy_len)"
  assumes abs: "enc_cache_abs s c_out"
      and cache_wf: "enc_cache_wf c_out"
      and bm: "best_mode' copy_addr here s = Some m"
      and pend_ge: "(1 :: 32 word) \<le> pend_len"
      and pend_le: "pend_len \<le> (4 :: 32 word)"
      and copy_ge: "(4 :: 32 word) \<le> copy_len"
      and mode_le: "mode_t_C.mode_C m \<le> (5 :: 32 word)"
      and addr_size: "varint_size' (mode_t_C.arg_C m) s = Some an"
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
      and addr_varint_fits:
        "\<not> addr_cap - sections_t_C.addr_pos_C sec < an"
      and addr_varint_valid: "\<forall>j < unat an.
        ptr_valid (heap_typing s)
          (addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j))"
      and addr_varint_inj: "\<forall>i < unat an. \<forall>j < unat an.
        i \<noteq> j \<longrightarrow>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat i) \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + of_nat j)"
      and addr_varint_prefix_disj:
        "\<forall>k < unat (sections_t_C.addr_pos_C sec). \<forall>i.
        i < an \<longrightarrow>
        addr_buf +\<^sub>p int k \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_varint_no_overflow:
        "unat (sections_t_C.addr_pos_C sec) + unat an < 2 ^ 32"
      and addr_out1_disj: "\<forall>k < out1_n. \<forall>i.
        i < an \<longrightarrow>
        out1 +\<^sub>p int k \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
      and addr_out2_disj: "\<forall>k < out2_n. \<forall>i.
        i < an \<longrightarrow>
        out2 +\<^sub>p int k \<noteq>
        addr_buf +\<^sub>p uint (sections_t_C.addr_pos_C sec + i)"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
           \<lbrace> \<lambda>r t.
              (\<exists>f.
                r = Result f \<and>
                fused_t_C.fused_C f = csz \<and>
                heap_bytes t out1 out1_n =
                  heap_bytes s out1 out1_n \<and>
                heap_bytes t out2 out2_n =
                  heap_bytes s out2 out2_n \<and>
                enc_cache_abs t (cache_update c_out (unat copy_addr)) \<and>
                enc_cache_wf (cache_update c_out (unat copy_addr))) \<and>
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
  note gets_the_best_mode'_result[runs_to_vcg]
  note add_copy_opcode'_mode_le5[runs_to_vcg]
  show ?thesis
    unfolding try_emit_add_copy'_def csz_def
    using bm pend_ge pend_le copy_ge mode_le csz_ge csz_le sec_ok
    apply runs_to_vcg
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt word_le_nat_alt
                         word_neq_0_conv unat_word_ariths)
    using op_nz_gt6_expr apply simp
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
      apply (rule runs_to_weaken)
       apply (rule emit_address'_success_varint_preserves_heap_bytes2_cache_abs
         [where n = an])
                apply assumption
               apply assumption
              apply (rule mode_lt)
             subgoal for t cur
               using addr_size varint_size'_state_independent
                 [of "mode_t_C.arg_C m" cur s] by simp
            apply (rule addr_varint_fits)
           apply clarsimp
           using addr_varint_valid apply blast
          apply (rule addr_varint_inj)
         apply (rule addr_varint_prefix_disj)
        apply (rule addr_varint_no_overflow)
       apply (rule addr_out1_disj)
      apply (rule addr_out2_disj)
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF cache_update'_preserves_heap_bytes2_enc_cache_abs_wf[
          of _ _ _ out1 out1_n out2 out2_n]])
        apply assumption
       apply assumption
      apply clarsimp
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt word_le_nat_alt
                         word_neq_0_conv unat_word_ariths)
    using op_nz_le6_expr apply (auto simp: word_less_nat_alt)
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
      apply (rule runs_to_weaken)
       apply (rule emit_address'_success_varint_preserves_heap_bytes2_cache_abs
         [where n = an])
                apply assumption
               apply assumption
              apply (rule mode_lt)
             subgoal for t cur
               using addr_size varint_size'_state_independent
                 [of "mode_t_C.arg_C m" cur s] by simp
            apply (rule addr_varint_fits)
           apply clarsimp
           using addr_varint_valid apply blast
          apply (rule addr_varint_inj)
         apply (rule addr_varint_prefix_disj)
        apply (rule addr_varint_no_overflow)
       apply (rule addr_out1_disj)
      apply (rule addr_out2_disj)
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[
        OF cache_update'_preserves_heap_bytes2_enc_cache_abs_wf[
          of _ _ _ out1 out1_n out2 out2_n]])
        apply assumption
       apply assumption
      apply clarsimp
    done
qed

text \<open>Loop-context keystone for the fused ADD+COPY emit: given the loop
  invariant ingredients and a successful spec-side fusion, the C
  try_emit_add_copy' produces exactly the fused spec state, updates the
  cache, and frames src/tgt.  Dispatches over the four leaf lemmas
  (state_rel / cache_abs / emitted_sections / heap_bytes2_frame) for
  modes \<le>5 (varint address) and >5 (byte address).\<close>

lemma try_emit_add_copy'_state_rel_cache_frame_from_loop:
  fixes src tgt data inst addr pending :: "8 word ptr"
    and src_len_w tgt_len data_cap inst_cap addr_cap pending_cap :: "32 word"
    and copy_addr here copy_len pend_len :: "32 word"
    and src_len :: nat
  assumes buffers:
      "encode_window_loop_buffers_ok s src src_len_w tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and abs: "enc_cache_abs s (enc_cache spec_st)"
    and wf: "enc_cache_wf (enc_cache spec_st)"
    and pending_rel:
      "heap_bytes_word s pending 0 pend_len = enc_pending spec_st"
    and pending_len: "length (enc_pending spec_st) = unat pend_len"
    and pend_len_le: "unat pend_len \<le> unat pending_cap"
    and bm: "best_mode' copy_addr here s = Some bm_m"
    and addr_exact:
      "encode_address (enc_cache spec_st) (unat copy_addr)
         (src_len + enc_tp spec_st) =
       (unat (mode_t_C.mode_C bm_m),
        enc_best_bytes (mode_t_C.mode_C bm_m) (mode_t_C.arg_C bm_m),
        cache_update (enc_cache spec_st) (unat copy_addr))"
    and fused:
      "try_emit_add_copy_spec src_len (unat copy_addr) (unat copy_len)
         spec_st = Some spec_st'"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and data_room_spec: "length (enc_data spec_st') \<le> unat data_cap"
    and inst_room_spec: "length (enc_inst spec_st') \<le> unat inst_cap"
    and addr_room_spec: "length (enc_addr spec_st') \<le> unat addr_cap"
  shows "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
            pending pend_len copy_addr here copy_len \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>f.
              r = Result f \<and>
              fused_t_C.fused_C f \<noteq> 0 \<and>
              unat (fused_t_C.fused_C f) =
                enc_tp spec_st' - enc_tp spec_st \<and>
              sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK \<and>
              sections_t_C.data_pos_C (fused_t_C.s_C f) =
                sections_t_C.data_pos_C sec + pend_len \<and>
              enc_sections_state_rel t data inst addr
                (fused_t_C.s_C f) spec_st' \<and>
              enc_cache_abs t (enc_cache spec_st') \<and>
              enc_cache_wf (enc_cache spec_st') \<and>
              heap_bytes t src (unat src_len_w) =
                heap_bytes s src (unat src_len_w) \<and>
              heap_bytes t tgt (unat tgt_len) =
                heap_bytes s tgt (unat tgt_len) \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?dp = "sections_t_C.data_pos_C sec"
  let ?ip = "sections_t_C.inst_pos_C sec"
  let ?ap = "sections_t_C.addr_pos_C sec"
  let ?c1 = "cache_update (enc_cache spec_st) (unat copy_addr)"
  let ?csz = "(if (6 :: 32 word) < copy_len then (6 :: 32 word) else copy_len)"
  have src_valid: "buf_valid s src (unat src_len_w)"
    and tgt_valid: "buf_valid s tgt (unat tgt_len)"
    and pending_valid_buf: "buf_valid s pending (unat pending_cap)"
    and data_valid_buf: "buf_valid s data (unat data_cap)"
    and inst_valid: "buf_valid s inst (unat inst_cap)"
    and addr_valid: "buf_valid s addr (unat addr_cap)"
    and data_dist: "ptr_range_distinct data (unat data_cap)"
    and inst_dist: "ptr_range_distinct inst (unat inst_cap)"
    and addr_dist: "ptr_range_distinct addr (unat addr_cap)"
    and pending_data: "bufs_disjoint pending (unat pending_cap) data (unat data_cap)"
    and pending_inst: "bufs_disjoint pending (unat pending_cap) inst (unat inst_cap)"
    and data_src: "bufs_disjoint data (unat data_cap) src (unat src_len_w)"
    and data_tgt: "bufs_disjoint data (unat data_cap) tgt (unat tgt_len)"
    and data_inst: "bufs_disjoint data (unat data_cap) inst (unat inst_cap)"
    and data_addr: "bufs_disjoint data (unat data_cap) addr (unat addr_cap)"
    and inst_src: "bufs_disjoint inst (unat inst_cap) src (unat src_len_w)"
    and inst_tgt: "bufs_disjoint inst (unat inst_cap) tgt (unat tgt_len)"
    and inst_addr: "bufs_disjoint inst (unat inst_cap) addr (unat addr_cap)"
    and addr_src: "bufs_disjoint addr (unat addr_cap) src (unat src_len_w)"
    and addr_tgt: "bufs_disjoint addr (unat addr_cap) tgt (unat tgt_len)"
    using buffers by (auto simp: encode_window_loop_buffers_ok_def)
  have pend_ge_nat: "1 \<le> unat pend_len"
    and pend_le_nat: "unat pend_len \<le> 4"
    using fused pending_len
    by (auto simp: try_emit_add_copy_spec_def Let_def min_match_def
             split: option.splits prod.splits if_splits)
  have pend_ge: "(1 :: 32 word) \<le> pend_len"
    using pend_ge_nat by (simp add: word_le_nat_alt)
  have pend_le: "pend_len \<le> (4 :: 32 word)"
    using pend_le_nat by (simp add: word_le_nat_alt)
  have copy_ge_nat: "4 \<le> unat copy_len"
    using fused
    by (auto simp: try_emit_add_copy_spec_def Let_def min_match_def
             split: option.splits prod.splits if_splits)
  have copy_ge: "(4 :: 32 word) \<le> copy_len"
    using copy_ge_nat by (simp add: word_le_nat_alt)
  have mode_wf:
    "enc_mode_arg_wf (enc_cache spec_st) copy_addr here bm_m"
    by (rule best_mode'_encode_address_correct[OF abs wf bm])
  have mode_le8: "mode_t_C.mode_C bm_m \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  obtain an where addr_size: "varint_size' (mode_t_C.arg_C bm_m) s = Some an"
    using varint_size'_some by blast
  have an_le5: "unat an \<le> 5" by (rule varint_size'_le5[OF addr_size])
  have near_ptr_lt: "near_ptr_'' s < (4 :: 32 word)"
    by (rule enc_cache_abs_near_ptr_lt_word[OF abs])
  have addr_choice_gt5:
    "\<not> mode_t_C.mode_C bm_m < (6 :: 32 word) \<Longrightarrow>
     encode_address (enc_cache spec_st) (unat copy_addr)
       (src_len + enc_tp spec_st) =
     (unat (mode_t_C.mode_C bm_m), [ucast (mode_t_C.arg_C bm_m)], ?c1)"
    using addr_exact by (simp add: enc_best_bytes_def)
  have addr_choice_le5:
    "mode_t_C.mode_C bm_m < (6 :: 32 word) \<Longrightarrow>
     encode_address (enc_cache spec_st) (unat copy_addr)
       (src_len + enc_tp spec_st) =
     (unat (mode_t_C.mode_C bm_m),
      varint_bytes32 (mode_t_C.arg_C bm_m) an, ?c1)"
    using addr_exact varint_bytes32_eq_varint_encode[OF addr_size]
    by (simp add: enc_best_bytes_def)
  have emitted:
    "emitted_sections s data inst addr sec
      (enc_data spec_st) (enc_inst spec_st) (enc_addr spec_st)"
    using rel by (simp add: enc_sections_state_rel_def)
  have dp_len: "length (enc_data spec_st) = unat ?dp"
    and ip_len: "length (enc_inst spec_st) = unat ?ip"
    and ap_len: "length (enc_addr spec_st) = unat ?ap"
    using enc_sections_state_rel_lengths[OF rel] by simp_all
  show ?thesis
  proof (cases "mode_t_C.mode_C bm_m \<le> (5 :: 32 word)")
    case mode_le5: True
    have mode_lt6: "mode_t_C.mode_C bm_m < (6 :: 32 word)"
      using mode_le5 by (simp add: word_le_nat_alt word_less_nat_alt)
    note ac5 = addr_choice_le5[OF mode_lt6]
    let ?op5 = "(163 + mode_t_C.mode_C bm_m * 12 + (pend_len - 1) * 3 +
                 (?csz - 4) :: 32 word)"
    have csz_ge: "(4 :: 32 word) \<le> ?csz"
      using copy_ge by (auto simp: word_less_nat_alt word_le_nat_alt)
    have csz_nz: "?csz \<noteq> 0"
    proof
      assume "?csz = 0"
      thus False using csz_ge by simp
    qed
    have spec_eq: "spec_st' =
      spec_st \<lparr> enc_tp := enc_tp spec_st + unat ?csz
              , enc_flushed :=
                  enc_flushed spec_st + unat pend_len + unat ?csz
              , enc_pending := []
              , enc_data := enc_data spec_st @ enc_pending spec_st
              , enc_inst := enc_inst spec_st @ [ucast ?op5]
              , enc_addr := enc_addr spec_st @
                  varint_bytes32 (mode_t_C.arg_C bm_m) an
              , enc_cache := ?c1
              , enc_trace := enc_trace spec_st
                  @ [RAdd (enc_pending spec_st),
                     RCopy (unat copy_addr) (unat ?csz)] \<rparr>"
      using fused
        try_emit_add_copy_spec_mode_le5_success[
          OF pending_len pend_ge pend_le copy_ge mode_le5 ac5]
      by simp
    have tp_diff: "enc_tp spec_st' - enc_tp spec_st = unat ?csz"
      using spec_eq by simp
    have cache'_eq: "enc_cache spec_st' = ?c1"
      using spec_eq by simp
    have abl: "length (varint_bytes32 (mode_t_C.arg_C bm_m) an) = unat an"
      using an_le5 by (simp add: varint_bytes32_def)
    have DP: "unat ?dp + unat pend_len \<le> unat data_cap"
      using data_room_spec spec_eq dp_len pending_len by simp
    have IP1: "unat ?ip + 1 \<le> unat inst_cap"
      using inst_room_spec spec_eq ip_len by simp
    have AN: "unat ?ap + unat an \<le> unat addr_cap"
      using addr_room_spec spec_eq ap_len abl by simp
    have IL: "unat ?ip < unat inst_cap" using IP1 by linarith
    have ILW: "?ip < inst_cap" using IL by (simp add: word_less_nat_alt)
    have isu: "unat (?ip + 1) = unat ?ip + 1"
      using IP1 unat_lt2p[of inst_cap] by unat_arith
    have IP1': "unat (?ip + 1) \<le> unat inst_cap" using isu IP1 by simp
    have dp_no: "unat ?dp + unat pend_len < 2 ^ 32"
      using DP unat_lt2p[of data_cap] by simp
    have dpu: "unat (?dp + pend_len) = unat ?dp + unat pend_len"
      using DP unat_lt2p[of data_cap] by unat_arith
    have dp_le: "unat ?dp \<le> unat data_cap" using DP by linarith
    have ap_no: "unat ?ap + unat an < 2 ^ 32"
      using AN unat_lt2p[of addr_cap] by simp
    have ap_le: "unat ?ap \<le> unat addr_cap" using AN by linarith
    \<comment> \<open>--- disjointness / validity facts for the leaf lemmas ---\<close>
    have IBP: "ptr_valid (heap_typing s) (inst +\<^sub>p uint ?ip)"
      by (rule buf_valid_uintD[OF inst_valid IL])
    have IBD: "ptr_range_distinct inst (Suc (unat ?ip))"
      by (rule ptr_range_distinct_mono[OF inst_dist]) (simp add: Suc_le_eq IL)
    have IBDD: "\<forall>i < unat ?dp. data +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat ?dp"
      have "i < unat data_cap" using i_lt dp_le by linarith
      thus "data +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_int_uintD[OF data_inst _ IL])
    qed
    have IBAD: "\<forall>i < unat ?ap. addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat ?ap"
      have "i < unat addr_cap" using i_lt ap_le by linarith
      thus "addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_int_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF inst_addr] _ IL])
    qed
    have IBPD: "\<forall>i < unat pend_len.
        pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat pend_len"
      have i32: "i < 2 ^ 32"
        using i_lt unat_lt2p[of pend_len] by simp
      have iu: "unat (of_nat i :: 32 word) = i"
        using i32 by (simp add: unat_of_nat_eq)
      have "unat (of_nat i :: 32 word) < unat pending_cap"
        using iu i_lt pend_len_le by linarith
      thus "pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_uint_uintD[OF pending_inst _ IL])
    qed
    have DF: "\<not> data_cap - ?dp < pend_len"
      by (rule word_sub_not_less_of_unat_add_le[OF DP])
    have DV: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s) (data +\<^sub>p uint (?dp + of_nat j))"
    proof (intro allI impI)
      fix j assume j_lt: "j < unat pend_len"
      show "ptr_valid (heap_typing s) (data +\<^sub>p uint (?dp + of_nat j))"
        by (rule buf_valid_word_rangeD[OF data_valid_buf j_lt dp_no DP])
    qed
    have PV: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s) (pending +\<^sub>p uint (of_nat j :: 32 word))"
      using encode_window_loop_buffers_ok_pending_ptr_valid[
          OF buffers pend_len_le]
      by simp
    have DPD: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        data +\<^sub>p uint (?dp + of_nat i) \<noteq>
        pending +\<^sub>p uint (of_nat j :: 32 word)"
    proof (intro allI impI)
      fix i j assume i_lt: "i < unat pend_len" and j_lt: "j < unat pend_len"
      have iu: "unat (?dp + of_nat i) = unat ?dp + i"
        using i_lt dp_no DP unat_lt2p[of data_cap]
        by (simp add: unat_word_ariths unat_of_nat_eq)
      have i_cap: "unat (?dp + of_nat i) < unat data_cap"
        using iu i_lt DP by linarith
      have j32: "j < 2 ^ 32" using j_lt unat_lt2p[of pend_len] by simp
      have ju: "unat (of_nat j :: 32 word) = j"
        using j32 by (simp add: unat_of_nat_eq)
      have j_cap: "unat (of_nat j :: 32 word) < unat pending_cap"
        using ju j_lt pend_len_le by linarith
      show "data +\<^sub>p uint (?dp + of_nat i) \<noteq>
            pending +\<^sub>p uint (of_nat j :: 32 word)"
        by (rule bufs_disjoint_uint_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF pending_data] i_cap j_cap])
    qed
    have DI: "\<forall>i < unat pend_len. \<forall>j < unat pend_len. i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (?dp + of_nat i) \<noteq> data +\<^sub>p uint (?dp + of_nat j)"
    proof (intro allI impI)
      fix i j assume i_lt: "i < unat pend_len" and j_lt: "j < unat pend_len"
        and ne: "i \<noteq> j"
      show "data +\<^sub>p uint (?dp + of_nat i) \<noteq> data +\<^sub>p uint (?dp + of_nat j)"
      proof
        assume "data +\<^sub>p uint (?dp + of_nat i) = data +\<^sub>p uint (?dp + of_nat j)"
        hence "i = j"
          by (rule ptr_range_distinct_word_range_inj[
                OF data_dist dp_no DP i_lt j_lt])
        thus False using ne by simp
      qed
    qed
    have DPD2: "\<forall>k < unat ?dp. \<forall>i. i < pend_len \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat ?dp" and i_lt: "i < pend_len"
      show "data +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule ptr_range_distinct_word_prefix_disj[
              OF data_dist dp_no DP k_lt i_lt])
    qed
    have DID: "\<forall>k < unat (?ip + 1). \<forall>i. i < pend_len \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat (?ip + 1)" and i_lt: "i < pend_len"
      have k_cap: "k < unat inst_cap" using k_lt IP1' by linarith
      show "inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF data_inst]
                 k_cap i_lt dp_no DP])
    qed
    have DAD: "\<forall>k < unat ?ap. \<forall>i. i < pend_len \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat ?ap" and i_lt: "i < pend_len"
      have k_cap: "k < unat addr_cap" using k_lt ap_le by linarith
      show "addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF data_addr]
                 k_cap i_lt dp_no DP])
    qed
    have AVF: "\<not> addr_cap - ?ap < an"
      by (rule word_sub_not_less_of_unat_add_le[OF AN])
    have AVV: "\<forall>j < unat an.
        ptr_valid (heap_typing s) (addr +\<^sub>p uint (?ap + of_nat j))"
    proof (intro allI impI)
      fix j assume j_lt: "j < unat an"
      show "ptr_valid (heap_typing s) (addr +\<^sub>p uint (?ap + of_nat j))"
        by (rule buf_valid_word_rangeD[OF addr_valid j_lt ap_no AN])
    qed
    have AVI: "\<forall>i < unat an. \<forall>j < unat an. i \<noteq> j \<longrightarrow>
        addr +\<^sub>p uint (?ap + of_nat i) \<noteq> addr +\<^sub>p uint (?ap + of_nat j)"
    proof (intro allI impI)
      fix i j assume i_lt: "i < unat an" and j_lt: "j < unat an"
        and ne: "i \<noteq> j"
      show "addr +\<^sub>p uint (?ap + of_nat i) \<noteq> addr +\<^sub>p uint (?ap + of_nat j)"
      proof
        assume "addr +\<^sub>p uint (?ap + of_nat i) = addr +\<^sub>p uint (?ap + of_nat j)"
        hence "i = j"
          by (rule ptr_range_distinct_word_range_inj[
                OF addr_dist ap_no AN i_lt j_lt])
        thus False using ne by simp
      qed
    qed
    have AVP: "\<forall>k < unat ?ap. \<forall>i. i < an \<longrightarrow>
        addr +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat ?ap" and i_lt: "i < an"
      show "addr +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
        by (rule ptr_range_distinct_word_prefix_disj[
              OF addr_dist ap_no AN k_lt i_lt])
    qed
    have AVDD: "\<forall>k < unat (?dp + pend_len). \<forall>i. i < an \<longrightarrow>
        data +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat (?dp + pend_len)" and i_lt: "i < an"
      have k_cap: "k < unat data_cap" using k_lt dpu DP by linarith
      show "data +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF data_addr k_cap i_lt ap_no AN])
    qed
    have AVID: "\<forall>k < unat (?ip + 1). \<forall>i. i < an \<longrightarrow>
        inst +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat (?ip + 1)" and i_lt: "i < an"
      have k_cap: "k < unat inst_cap" using k_lt IP1' by linarith
      show "inst +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF inst_addr k_cap i_lt ap_no AN])
    qed
    have SIB: "\<forall>i < unat src_len_w. src +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat src_len_w"
      show "src +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_int_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF inst_src] i_lt IL])
    qed
    have TIB: "\<forall>i < unat tgt_len. tgt +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat tgt_len"
      show "tgt +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_int_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF inst_tgt] i_lt IL])
    qed
    have SDD: "\<forall>k < unat src_len_w. \<forall>i. i < pend_len \<longrightarrow>
        src +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat src_len_w" and i_lt: "i < pend_len"
      show "src +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF data_src]
                 k_lt i_lt dp_no DP])
    qed
    have TDD: "\<forall>k < unat tgt_len. \<forall>i. i < pend_len \<longrightarrow>
        tgt +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat tgt_len" and i_lt: "i < pend_len"
      show "tgt +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF data_tgt]
                 k_lt i_lt dp_no DP])
    qed
    have SAV: "\<forall>k < unat src_len_w. \<forall>i. i < an \<longrightarrow>
        src +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat src_len_w" and i_lt: "i < an"
      show "src +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF addr_src]
                 k_lt i_lt ap_no AN])
    qed
    have TAV: "\<forall>k < unat tgt_len. \<forall>i. i < an \<longrightarrow>
        tgt +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat tgt_len" and i_lt: "i < an"
      show "tgt +\<^sub>p int k \<noteq> addr +\<^sub>p uint (?ap + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF addr_tgt]
                 k_lt i_lt ap_no AN])
    qed
    \<comment> \<open>--- the four leaf runs_to facts ---\<close>
    have srel:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            (\<exists>f spec_stx.
              r = Result f \<and>
              fused_t_C.fused_C f = ?csz \<and>
              try_emit_add_copy_spec src_len (unat copy_addr)
                (unat copy_len) spec_st = Some spec_stx \<and>
              enc_sections_state_rel t data inst addr
                (fused_t_C.s_C f) spec_stx) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule try_emit_add_copy'_mode_le5_success_enc_sections_state_rel[
            OF rel abs wf bm pending_rel[symmetric] pend_ge pend_le copy_ge
               mode_le5 addr_size ac5 sec_ok
               ILW IBP IBD IBDD IBAD IBPD
               DF DV PV DPD DI DPD2 dp_no DID DAD
               AVF AVV AVI AVP ap_no AVDD AVID])
    have cache:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            (\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = ?csz \<and>
                 enc_cache_abs t ?c1 \<and>
                 enc_cache_wf ?c1) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule try_emit_add_copy'_mode_le5_success_enc_cache_abs[
            OF abs wf bm pend_ge pend_le copy_ge mode_le5 addr_size sec_ok
               ILW IBP DF DV PV AVF AVV])
    have emitf:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            (\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = ?csz \<and>
                 sections_result (fused_t_C.s_C f)
                   (?dp + pend_len) (?ip + 1) (?ap + an) ENC_OK \<and>
                 emitted_sections t data inst addr (fused_t_C.s_C f)
                   (enc_data spec_st @ heap_bytes_word s pending 0 pend_len)
                   (enc_inst spec_st @ [ucast ?op5])
                   (enc_addr spec_st @
                      varint_bytes32 (mode_t_C.arg_C bm_m) an)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule try_emit_add_copy'_mode_le5_success_emitted_sections[
            OF emitted bm pend_ge pend_le copy_ge mode_le5 addr_size sec_ok
               near_ptr_lt
               ILW IBP IBD IBDD IBAD IBPD
               DF DV PV DPD DI DPD2 dp_no DID DAD
               AVF AVV AVI AVP ap_no AVDD AVID])
    have frame:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            (\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = ?csz \<and>
                 heap_bytes t src (unat src_len_w) =
                   heap_bytes s src (unat src_len_w) \<and>
                 heap_bytes t tgt (unat tgt_len) =
                   heap_bytes s tgt (unat tgt_len) \<and>
                 enc_cache_abs t ?c1 \<and>
                 enc_cache_wf ?c1) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule try_emit_add_copy'_mode_le5_success_heap_bytes2_cache_frame[
            OF abs wf bm pend_ge pend_le copy_ge mode_le5 addr_size sec_ok
               ILW IBP SIB TIB
               DF DV PV SDD TDD
               AVF AVV AVI AVP ap_no SAV TAV])
    have comb:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            ((\<exists>f spec_stx.
              r = Result f \<and>
              fused_t_C.fused_C f = ?csz \<and>
              try_emit_add_copy_spec src_len (unat copy_addr)
                (unat copy_len) spec_st = Some spec_stx \<and>
              enc_sections_state_rel t data inst addr
                (fused_t_C.s_C f) spec_stx) \<and>
            heap_typing t = heap_typing s) \<and>
            ((\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = ?csz \<and>
                 enc_cache_abs t ?c1 \<and>
                 enc_cache_wf ?c1) \<and>
            heap_typing t = heap_typing s) \<and>
            ((\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = ?csz \<and>
                 sections_result (fused_t_C.s_C f)
                   (?dp + pend_len) (?ip + 1) (?ap + an) ENC_OK \<and>
                 emitted_sections t data inst addr (fused_t_C.s_C f)
                   (enc_data spec_st @ heap_bytes_word s pending 0 pend_len)
                   (enc_inst spec_st @ [ucast ?op5])
                   (enc_addr spec_st @
                      varint_bytes32 (mode_t_C.arg_C bm_m) an)) \<and>
            heap_typing t = heap_typing s) \<and>
            ((\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = ?csz \<and>
                 heap_bytes t src (unat src_len_w) =
                   heap_bytes s src (unat src_len_w) \<and>
                 heap_bytes t tgt (unat tgt_len) =
                   heap_bytes s tgt (unat tgt_len) \<and>
                 enc_cache_abs t ?c1 \<and>
                 enc_cache_wf ?c1) \<and>
            heap_typing t = heap_typing s) \<rbrace>"
      using srel cache emitf frame by (simp add: runs_to_conj)
    show ?thesis
    proof (rule runs_to_weaken[OF comb])
      fix r t
      assume H:
        "((\<exists>f spec_stx.
            r = Result f \<and>
            fused_t_C.fused_C f = ?csz \<and>
            try_emit_add_copy_spec src_len (unat copy_addr)
              (unat copy_len) spec_st = Some spec_stx \<and>
            enc_sections_state_rel t data inst addr
              (fused_t_C.s_C f) spec_stx) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>f. r = Result f \<and>
               fused_t_C.fused_C f = ?csz \<and>
               enc_cache_abs t ?c1 \<and>
               enc_cache_wf ?c1) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>f. r = Result f \<and>
               fused_t_C.fused_C f = ?csz \<and>
               sections_result (fused_t_C.s_C f)
                 (?dp + pend_len) (?ip + 1) (?ap + an) ENC_OK \<and>
               emitted_sections t data inst addr (fused_t_C.s_C f)
                 (enc_data spec_st @ heap_bytes_word s pending 0 pend_len)
                 (enc_inst spec_st @ [ucast ?op5])
                 (enc_addr spec_st @
                    varint_bytes32 (mode_t_C.arg_C bm_m) an)) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>f. r = Result f \<and>
               fused_t_C.fused_C f = ?csz \<and>
               heap_bytes t src (unat src_len_w) =
                 heap_bytes s src (unat src_len_w) \<and>
               heap_bytes t tgt (unat tgt_len) =
                 heap_bytes s tgt (unat tgt_len) \<and>
               enc_cache_abs t ?c1 \<and>
               enc_cache_wf ?c1) \<and>
          heap_typing t = heap_typing s)"
      obtain f spec_stx where
          rf: "r = Result f"
        and fz: "fused_t_C.fused_C f = ?csz"
        and somex: "try_emit_add_copy_spec src_len (unat copy_addr)
              (unat copy_len) spec_st = Some spec_stx"
        and srelx: "enc_sections_state_rel t data inst addr
              (fused_t_C.s_C f) spec_stx"
        and typing: "heap_typing t = heap_typing s"
        using H by blast
      have spx: "spec_stx = spec_st'" using somex fused by simp
      obtain f2 where rf2: "r = Result f2"
        and cabs: "enc_cache_abs t ?c1" and cwf: "enc_cache_wf ?c1"
        using H by blast
      obtain f3 where rf3: "r = Result f3"
        and secres: "sections_result (fused_t_C.s_C f3)
              (?dp + pend_len) (?ip + 1) (?ap + an) ENC_OK"
        using H by blast
      have f3f: "f3 = f" using rf rf3 by simp
      obtain f4 where rf4: "r = Result f4"
        and src_frame: "heap_bytes t src (unat src_len_w) =
              heap_bytes s src (unat src_len_w)"
        and tgt_frame: "heap_bytes t tgt (unat tgt_len) =
              heap_bytes s tgt (unat tgt_len)"
        using H by blast
      show "\<exists>f. r = Result f \<and>
              fused_t_C.fused_C f \<noteq> 0 \<and>
              unat (fused_t_C.fused_C f) =
                enc_tp spec_st' - enc_tp spec_st \<and>
              sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK \<and>
              sections_t_C.data_pos_C (fused_t_C.s_C f) = ?dp + pend_len \<and>
              enc_sections_state_rel t data inst addr
                (fused_t_C.s_C f) spec_st' \<and>
              enc_cache_abs t (enc_cache spec_st') \<and>
              enc_cache_wf (enc_cache spec_st') \<and>
              heap_bytes t src (unat src_len_w) =
                heap_bytes s src (unat src_len_w) \<and>
              heap_bytes t tgt (unat tgt_len) =
                heap_bytes s tgt (unat tgt_len) \<and>
              heap_typing t = heap_typing s"
        using rf fz csz_nz tp_diff secres f3f srelx spx cabs cwf cache'_eq
          src_frame tgt_frame typing spec_eq
        by (auto simp: sections_result_def)
    qed
  next
    case False
    have mode_gt: "(5 :: 32 word) < mode_t_C.mode_C bm_m"
      using False by (simp add: word_le_nat_alt word_less_nat_alt)
    have mode_ge6: "\<not> mode_t_C.mode_C bm_m < (6 :: 32 word)"
      using mode_gt by (simp add: word_less_nat_alt)
    note ac8 = addr_choice_gt5[OF mode_ge6]
    have copy_eq: "copy_len = (4 :: 32 word)"
    proof (rule ccontr)
      assume ne: "copy_len \<noteq> (4 :: 32 word)"
      have "try_emit_add_copy_spec src_len (unat copy_addr)
              (unat copy_len) spec_st = None"
        by (rule try_emit_add_copy_spec_mode_gt5_copy_ne4_none[
              OF addr_exact mode_gt ne])
      thus False using fused by simp
    qed
    have csz_eq4: "?csz = copy_len"
      using copy_eq by simp
    let ?op8 = "(235 + (mode_t_C.mode_C bm_m - 6) * 4 + (pend_len - 1) ::
                32 word)"
    have spec_eq: "spec_st' =
      spec_st \<lparr> enc_tp := enc_tp spec_st + unat copy_len
              , enc_flushed :=
                  enc_flushed spec_st + unat pend_len + unat copy_len
              , enc_pending := []
              , enc_data := enc_data spec_st @ enc_pending spec_st
              , enc_inst := enc_inst spec_st @ [ucast ?op8]
              , enc_addr := enc_addr spec_st @ [ucast (mode_t_C.arg_C bm_m)]
              , enc_cache := ?c1
              , enc_trace := enc_trace spec_st
                  @ [RAdd (enc_pending spec_st),
                     RCopy (unat copy_addr) (unat copy_len)] \<rparr>"
      using fused
        try_emit_add_copy_spec_mode_gt5_success[
          OF pending_len pend_ge pend_le copy_eq mode_gt mode_le8 ac8]
      by simp
    have tp_diff: "enc_tp spec_st' - enc_tp spec_st = unat copy_len"
      using spec_eq by simp
    have cache'_eq: "enc_cache spec_st' = ?c1"
      using spec_eq by simp
    have copy_nz: "copy_len \<noteq> 0"
      using copy_eq by simp
    have DP: "unat ?dp + unat pend_len \<le> unat data_cap"
      using data_room_spec spec_eq dp_len pending_len by simp
    have IP1: "unat ?ip + 1 \<le> unat inst_cap"
      using inst_room_spec spec_eq ip_len by simp
    have AP1: "unat ?ap + 1 \<le> unat addr_cap"
      using addr_room_spec spec_eq ap_len by simp
    have IL: "unat ?ip < unat inst_cap" using IP1 by linarith
    have ILW: "?ip < inst_cap" using IL by (simp add: word_less_nat_alt)
    have isu: "unat (?ip + 1) = unat ?ip + 1"
      using IP1 unat_lt2p[of inst_cap] by unat_arith
    have IP1': "unat (?ip + 1) \<le> unat inst_cap" using isu IP1 by simp
    have AL: "unat ?ap < unat addr_cap" using AP1 by linarith
    have ALW: "?ap < addr_cap" using AL by (simp add: word_less_nat_alt)
    have dp_no: "unat ?dp + unat pend_len < 2 ^ 32"
      using DP unat_lt2p[of data_cap] by simp
    have dpu: "unat (?dp + pend_len) = unat ?dp + unat pend_len"
      using DP unat_lt2p[of data_cap] by unat_arith
    have dp_le: "unat ?dp \<le> unat data_cap" using DP by linarith
    \<comment> \<open>--- disjointness / validity facts ---\<close>
    have IBP: "ptr_valid (heap_typing s) (inst +\<^sub>p uint ?ip)"
      by (rule buf_valid_uintD[OF inst_valid IL])
    have IBD: "ptr_range_distinct inst (Suc (unat ?ip))"
      by (rule ptr_range_distinct_mono[OF inst_dist]) (simp add: Suc_le_eq IL)
    have IBDD: "\<forall>i < unat ?dp. data +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat ?dp"
      have "i < unat data_cap" using i_lt dp_le by linarith
      thus "data +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_int_uintD[OF data_inst _ IL])
    qed
    have IBAD: "\<forall>i < unat ?ap. addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat ?ap"
      have "i < unat addr_cap" using i_lt AL by linarith
      thus "addr +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_int_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF inst_addr] _ IL])
    qed
    have IBPD: "\<forall>i < unat pend_len.
        pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat pend_len"
      have i32: "i < 2 ^ 32"
        using i_lt unat_lt2p[of pend_len] by simp
      have iu: "unat (of_nat i :: 32 word) = i"
        using i32 by (simp add: unat_of_nat_eq)
      have "unat (of_nat i :: 32 word) < unat pending_cap"
        using iu i_lt pend_len_le by linarith
      thus "pending +\<^sub>p uint (of_nat i :: 32 word) \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_uint_uintD[OF pending_inst _ IL])
    qed
    have DF: "\<not> data_cap - ?dp < pend_len"
      by (rule word_sub_not_less_of_unat_add_le[OF DP])
    have DV: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s) (data +\<^sub>p uint (?dp + of_nat j))"
    proof (intro allI impI)
      fix j assume j_lt: "j < unat pend_len"
      show "ptr_valid (heap_typing s) (data +\<^sub>p uint (?dp + of_nat j))"
        by (rule buf_valid_word_rangeD[OF data_valid_buf j_lt dp_no DP])
    qed
    have PV: "\<forall>j < unat pend_len.
        ptr_valid (heap_typing s) (pending +\<^sub>p uint (of_nat j :: 32 word))"
      using encode_window_loop_buffers_ok_pending_ptr_valid[
          OF buffers pend_len_le]
      by simp
    have DPD: "\<forall>i < unat pend_len. \<forall>j < unat pend_len.
        data +\<^sub>p uint (?dp + of_nat i) \<noteq>
        pending +\<^sub>p uint (of_nat j :: 32 word)"
    proof (intro allI impI)
      fix i j assume i_lt: "i < unat pend_len" and j_lt: "j < unat pend_len"
      have iu: "unat (?dp + of_nat i) = unat ?dp + i"
        using i_lt dp_no DP unat_lt2p[of data_cap]
        by (simp add: unat_word_ariths unat_of_nat_eq)
      have i_cap: "unat (?dp + of_nat i) < unat data_cap"
        using iu i_lt DP by linarith
      have j32: "j < 2 ^ 32" using j_lt unat_lt2p[of pend_len] by simp
      have ju: "unat (of_nat j :: 32 word) = j"
        using j32 by (simp add: unat_of_nat_eq)
      have j_cap: "unat (of_nat j :: 32 word) < unat pending_cap"
        using ju j_lt pend_len_le by linarith
      show "data +\<^sub>p uint (?dp + of_nat i) \<noteq>
            pending +\<^sub>p uint (of_nat j :: 32 word)"
        by (rule bufs_disjoint_uint_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF pending_data] i_cap j_cap])
    qed
    have DI: "\<forall>i < unat pend_len. \<forall>j < unat pend_len. i \<noteq> j \<longrightarrow>
        data +\<^sub>p uint (?dp + of_nat i) \<noteq> data +\<^sub>p uint (?dp + of_nat j)"
    proof (intro allI impI)
      fix i j assume i_lt: "i < unat pend_len" and j_lt: "j < unat pend_len"
        and ne: "i \<noteq> j"
      show "data +\<^sub>p uint (?dp + of_nat i) \<noteq> data +\<^sub>p uint (?dp + of_nat j)"
      proof
        assume "data +\<^sub>p uint (?dp + of_nat i) = data +\<^sub>p uint (?dp + of_nat j)"
        hence "i = j"
          by (rule ptr_range_distinct_word_range_inj[
                OF data_dist dp_no DP i_lt j_lt])
        thus False using ne by simp
      qed
    qed
    have DPD2: "\<forall>k < unat ?dp. \<forall>i. i < pend_len \<longrightarrow>
        data +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat ?dp" and i_lt: "i < pend_len"
      show "data +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule ptr_range_distinct_word_prefix_disj[
              OF data_dist dp_no DP k_lt i_lt])
    qed
    have DID: "\<forall>k < unat (?ip + 1). \<forall>i. i < pend_len \<longrightarrow>
        inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat (?ip + 1)" and i_lt: "i < pend_len"
      have k_cap: "k < unat inst_cap" using k_lt IP1' by linarith
      show "inst +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF data_inst]
                 k_cap i_lt dp_no DP])
    qed
    have DAD: "\<forall>k < unat ?ap. \<forall>i. i < pend_len \<longrightarrow>
        addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat ?ap" and i_lt: "i < pend_len"
      have k_cap: "k < unat addr_cap" using k_lt AL by linarith
      show "addr +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF data_addr]
                 k_cap i_lt dp_no DP])
    qed
    have ABP: "ptr_valid (heap_typing s) (addr +\<^sub>p uint ?ap)"
      by (rule buf_valid_uintD[OF addr_valid AL])
    have ABD: "ptr_range_distinct addr (Suc (unat ?ap))"
      by (rule ptr_range_distinct_mono[OF addr_dist]) (simp add: Suc_le_eq AL)
    have ABDD: "\<forall>i < unat (?dp + pend_len).
        data +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat (?dp + pend_len)"
      have "i < unat data_cap" using i_lt dpu DP by linarith
      thus "data +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
        by (rule bufs_disjoint_int_uintD[OF data_addr _ AL])
    qed
    have ABID: "\<forall>i < unat (?ip + 1). inst +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat (?ip + 1)"
      have "i < unat inst_cap" using i_lt IP1' by linarith
      thus "inst +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
        by (rule bufs_disjoint_int_uintD[OF inst_addr _ AL])
    qed
    have SIB: "\<forall>i < unat src_len_w. src +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat src_len_w"
      show "src +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_int_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF inst_src] i_lt IL])
    qed
    have TIB: "\<forall>i < unat tgt_len. tgt +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat tgt_len"
      show "tgt +\<^sub>p int i \<noteq> inst +\<^sub>p uint ?ip"
        by (rule bufs_disjoint_int_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF inst_tgt] i_lt IL])
    qed
    have SDD: "\<forall>k < unat src_len_w. \<forall>i. i < pend_len \<longrightarrow>
        src +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat src_len_w" and i_lt: "i < pend_len"
      show "src +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF data_src]
                 k_lt i_lt dp_no DP])
    qed
    have TDD: "\<forall>k < unat tgt_len. \<forall>i. i < pend_len \<longrightarrow>
        tgt +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
    proof (intro allI impI)
      fix k i assume k_lt: "k < unat tgt_len" and i_lt: "i < pend_len"
      show "tgt +\<^sub>p int k \<noteq> data +\<^sub>p uint (?dp + i)"
        by (rule bufs_disjoint_word_range_rightD_word[
              OF bufs_disjoint_sym[THEN iffD1, OF data_tgt]
                 k_lt i_lt dp_no DP])
    qed
    have SAB: "\<forall>i < unat src_len_w. src +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat src_len_w"
      show "src +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
        by (rule bufs_disjoint_int_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF addr_src] i_lt AL])
    qed
    have TAB: "\<forall>i < unat tgt_len. tgt +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
    proof (intro allI impI)
      fix i assume i_lt: "i < unat tgt_len"
      show "tgt +\<^sub>p int i \<noteq> addr +\<^sub>p uint ?ap"
        by (rule bufs_disjoint_int_uintD[
              OF bufs_disjoint_sym[THEN iffD1, OF addr_tgt] i_lt AL])
    qed
    \<comment> \<open>--- the four leaf runs_to facts ---\<close>
    have srel:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            (\<exists>f spec_stx.
              r = Result f \<and>
              fused_t_C.fused_C f = copy_len \<and>
              try_emit_add_copy_spec src_len (unat copy_addr)
                (unat copy_len) spec_st = Some spec_stx \<and>
              enc_sections_state_rel t data inst addr
                (fused_t_C.s_C f) spec_stx) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule try_emit_add_copy'_mode_gt5_success_enc_sections_state_rel[
            OF rel abs wf bm pending_rel[symmetric] pend_ge pend_le copy_eq
               mode_gt mode_le8 ac8 sec_ok
               ILW IBP IBD IBDD IBAD IBPD
               DF DV PV DPD DI DPD2 dp_no DID DAD
               ALW ABP ABD ABDD ABID])
    have cache:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            (\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = copy_len \<and>
                 enc_cache_abs t ?c1 \<and>
                 enc_cache_wf ?c1) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule try_emit_add_copy'_mode_gt5_success_enc_cache_abs[
            OF abs wf bm pend_ge pend_le copy_eq mode_gt mode_le8 sec_ok
               ILW IBP DF DV PV ALW ABP])
    have emitf:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            (\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = copy_len \<and>
                 sections_result (fused_t_C.s_C f)
                   (?dp + pend_len) (?ip + 1) (?ap + 1) ENC_OK \<and>
                 emitted_sections t data inst addr (fused_t_C.s_C f)
                   (enc_data spec_st @ heap_bytes_word s pending 0 pend_len)
                   (enc_inst spec_st @ [ucast ?op8])
                   (enc_addr spec_st @ [ucast (mode_t_C.arg_C bm_m)])) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule try_emit_add_copy'_mode_gt5_success_emitted_sections[
            OF emitted bm pend_ge pend_le copy_eq mode_gt mode_le8 sec_ok
               near_ptr_lt
               ILW IBP IBD IBDD IBAD IBPD
               DF DV PV DPD DI DPD2 dp_no DID DAD
               ALW ABP ABD ABDD ABID])
    have frame:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            (\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = copy_len \<and>
                 heap_bytes t src (unat src_len_w) =
                   heap_bytes s src (unat src_len_w) \<and>
                 heap_bytes t tgt (unat tgt_len) =
                   heap_bytes s tgt (unat tgt_len) \<and>
                 enc_cache_abs t ?c1 \<and>
                 enc_cache_wf ?c1) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule try_emit_add_copy'_mode_gt5_success_heap_bytes2_cache_frame[
            OF abs wf bm pend_ge pend_le copy_eq mode_gt mode_le8 sec_ok
               ILW IBP SIB TIB
               DF DV PV SDD TDD
               ALW ABP ABD SAB TAB])
    have comb:
      "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
          pending pend_len copy_addr here copy_len \<bullet> s
        \<lbrace> \<lambda>r t.
            ((\<exists>f spec_stx.
              r = Result f \<and>
              fused_t_C.fused_C f = copy_len \<and>
              try_emit_add_copy_spec src_len (unat copy_addr)
                (unat copy_len) spec_st = Some spec_stx \<and>
              enc_sections_state_rel t data inst addr
                (fused_t_C.s_C f) spec_stx) \<and>
            heap_typing t = heap_typing s) \<and>
            ((\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = copy_len \<and>
                 enc_cache_abs t ?c1 \<and>
                 enc_cache_wf ?c1) \<and>
            heap_typing t = heap_typing s) \<and>
            ((\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = copy_len \<and>
                 sections_result (fused_t_C.s_C f)
                   (?dp + pend_len) (?ip + 1) (?ap + 1) ENC_OK \<and>
                 emitted_sections t data inst addr (fused_t_C.s_C f)
                   (enc_data spec_st @ heap_bytes_word s pending 0 pend_len)
                   (enc_inst spec_st @ [ucast ?op8])
                   (enc_addr spec_st @ [ucast (mode_t_C.arg_C bm_m)])) \<and>
            heap_typing t = heap_typing s) \<and>
            ((\<exists>f. r = Result f \<and>
                 fused_t_C.fused_C f = copy_len \<and>
                 heap_bytes t src (unat src_len_w) =
                   heap_bytes s src (unat src_len_w) \<and>
                 heap_bytes t tgt (unat tgt_len) =
                   heap_bytes s tgt (unat tgt_len) \<and>
                 enc_cache_abs t ?c1 \<and>
                 enc_cache_wf ?c1) \<and>
            heap_typing t = heap_typing s) \<rbrace>"
      using srel cache emitf frame by (simp add: runs_to_conj)
    show ?thesis
    proof (rule runs_to_weaken[OF comb])
      fix r t
      assume H:
        "((\<exists>f spec_stx.
            r = Result f \<and>
            fused_t_C.fused_C f = copy_len \<and>
            try_emit_add_copy_spec src_len (unat copy_addr)
              (unat copy_len) spec_st = Some spec_stx \<and>
            enc_sections_state_rel t data inst addr
              (fused_t_C.s_C f) spec_stx) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>f. r = Result f \<and>
               fused_t_C.fused_C f = copy_len \<and>
               enc_cache_abs t ?c1 \<and>
               enc_cache_wf ?c1) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>f. r = Result f \<and>
               fused_t_C.fused_C f = copy_len \<and>
               sections_result (fused_t_C.s_C f)
                 (?dp + pend_len) (?ip + 1) (?ap + 1) ENC_OK \<and>
               emitted_sections t data inst addr (fused_t_C.s_C f)
                 (enc_data spec_st @ heap_bytes_word s pending 0 pend_len)
                 (enc_inst spec_st @ [ucast ?op8])
                 (enc_addr spec_st @ [ucast (mode_t_C.arg_C bm_m)])) \<and>
          heap_typing t = heap_typing s) \<and>
          ((\<exists>f. r = Result f \<and>
               fused_t_C.fused_C f = copy_len \<and>
               heap_bytes t src (unat src_len_w) =
                 heap_bytes s src (unat src_len_w) \<and>
               heap_bytes t tgt (unat tgt_len) =
                 heap_bytes s tgt (unat tgt_len) \<and>
               enc_cache_abs t ?c1 \<and>
               enc_cache_wf ?c1) \<and>
          heap_typing t = heap_typing s)"
      obtain f spec_stx where
          rf: "r = Result f"
        and fz: "fused_t_C.fused_C f = copy_len"
        and somex: "try_emit_add_copy_spec src_len (unat copy_addr)
              (unat copy_len) spec_st = Some spec_stx"
        and srelx: "enc_sections_state_rel t data inst addr
              (fused_t_C.s_C f) spec_stx"
        and typing: "heap_typing t = heap_typing s"
        using H by blast
      have spx: "spec_stx = spec_st'" using somex fused by simp
      obtain f2 where rf2: "r = Result f2"
        and cabs: "enc_cache_abs t ?c1" and cwf: "enc_cache_wf ?c1"
        using H by blast
      obtain f3 where rf3: "r = Result f3"
        and secres: "sections_result (fused_t_C.s_C f3)
              (?dp + pend_len) (?ip + 1) (?ap + 1) ENC_OK"
        using H by blast
      have f3f: "f3 = f" using rf rf3 by simp
      obtain f4 where rf4: "r = Result f4"
        and src_frame: "heap_bytes t src (unat src_len_w) =
              heap_bytes s src (unat src_len_w)"
        and tgt_frame: "heap_bytes t tgt (unat tgt_len) =
              heap_bytes s tgt (unat tgt_len)"
        using H by blast
      show "\<exists>f. r = Result f \<and>
              fused_t_C.fused_C f \<noteq> 0 \<and>
              unat (fused_t_C.fused_C f) =
                enc_tp spec_st' - enc_tp spec_st \<and>
              sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK \<and>
              sections_t_C.data_pos_C (fused_t_C.s_C f) = ?dp + pend_len \<and>
              enc_sections_state_rel t data inst addr
                (fused_t_C.s_C f) spec_st' \<and>
              enc_cache_abs t (enc_cache spec_st') \<and>
              enc_cache_wf (enc_cache spec_st') \<and>
              heap_bytes t src (unat src_len_w) =
                heap_bytes s src (unat src_len_w) \<and>
              heap_bytes t tgt (unat tgt_len) =
                heap_bytes s tgt (unat tgt_len) \<and>
              heap_typing t = heap_typing s"
        using rf fz copy_nz tp_diff secres f3f srelx spx cabs cwf cache'_eq
          src_frame tgt_frame typing spec_eq
        by (auto simp: sections_result_def)
    qed
  qed
qed

text \<open>Buffers-ok depends only on the heap typing, so it transports across
  any writes that preserve typing.\<close>

lemma encode_window_loop_buffers_ok_heap_typing:
  assumes buffers:
      "encode_window_loop_buffers_ok s src src_len tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and typing: "heap_typing t = heap_typing s"
  shows "encode_window_loop_buffers_ok t src src_len tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
  using buffers typing
  by (simp add: encode_window_loop_buffers_ok_def buf_valid_def)

text \<open>Pure shape facts about a successful fused spec step and about
  emit_copy_spec, used to re-establish the budget invariant.\<close>

lemma try_emit_add_copy_spec_Some_shape:
  assumes some: "try_emit_add_copy_spec sl ca cl st = Some st'"
  shows "enc_pending st' = []"
    and "enc_flushed st' =
         enc_flushed st + length (enc_pending st) + (enc_tp st' - enc_tp st)"
    and "length (enc_data st') =
         length (enc_data st) + length (enc_pending st)"
    and "length (enc_inst st') = length (enc_inst st) + 1"
  using some
  by (auto simp: try_emit_add_copy_spec_def fused_copy_len_spec_def
      Let_def min_match_def
      split: option.splits prod.splits if_splits)

lemma try_emit_add_copy_spec_Some_partial_six:
  assumes some: "try_emit_add_copy_spec sl ca cl st = Some st'"
      and partial: "enc_tp st' - enc_tp st < cl"
  shows "enc_tp st' - enc_tp st = 6"
  using some partial
  by (auto simp: try_emit_add_copy_spec_def fused_copy_len_spec_def
      Let_def min_match_def
      split: option.splits prod.splits if_splits)

lemma emit_copy_spec_components:
  "enc_pending (emit_copy_spec sl a l st) = enc_pending st"
  "enc_tp (emit_copy_spec sl a l st) = enc_tp st + l"
  "enc_flushed (emit_copy_spec sl a l st) = enc_flushed st + l"
  "enc_data (emit_copy_spec sl a l st) = enc_data st"
  by (auto simp: emit_copy_spec_def emit_inst_spec_def Let_def
      split: prod.splits)

lemma emit_copy_spec_cache_of_encode_address:
  assumes ea: "encode_address (enc_cache st) a (sl + enc_flushed st) =
               (md, ab, c')"
  shows "enc_cache (emit_copy_spec sl a l st) = c'"
  using ea
  by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def
      split: prod.splits)

lemma emit_copy_spec_inst_growth:
  assumes l_lt: "l < 2 ^ 32"
  shows "length (enc_inst (emit_copy_spec sl a l st)) \<le>
         length (enc_inst st) + 6"
proof -
  obtain md ab c' where ea:
    "encode_address (enc_cache st) a (sl + enc_flushed st) = (md, ab, c')"
    by (metis prod_cases3)
  obtain op needs where fo:
    "find_single_copy_opcode l md = (op, needs)"
    by (metis surj_pair)
  have vlen: "length (varint_encode l) \<le> 5"
    using varint_size_le_5_32[OF l_lt] by simp
  show ?thesis
    using ea fo vlen
    by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
qed



text \<open>The budget-tower fused-copy step: try_emit_add_copy' keystone for the
  fused emit, emit_copy' keystone for the (possibly short) remainder copy,
  budget preservation via the pure match-step lemma.\<close>

lemma encode_window_try_fused_copy_step_topdown:
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
proof -
  let ?Q = "\<lambda>r t. \<exists>sec' tp' pend_len' spec_st''.
              r = Result (pend_len', sec', tp') \<and>
              encode_window_loop_budget_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st'' \<and>
              enc_tp spec_st < enc_tp spec_st'' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp)"
  let ?idx = "build_index_spec src_bytes"
  let ?mp = "match_t_C.pos_C m"
  let ?ml = "match_t_C.len_C m"
  \<comment> \<open>--- components of the budget invariant ---\<close>
  have src_heap: "heap_bytes s src (unat src_len) = src_bytes"
    and tgt_heap: "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
    and src_len_eq: "length src_bytes = unat src_len"
    and tgt_len_eq: "length tgt_bytes = unat tgt_len"
    and pending_heap:
      "heap_bytes_word s pending 0 pend_len = enc_pending spec_st"
    and pending_len: "length (enc_pending spec_st) = unat pend_len"
    and tp_eq: "enc_tp spec_st = unat tp"
    and flushed_inv:
      "enc_flushed spec_st + length (enc_pending spec_st) = enc_tp spec_st"
    and sections_rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and pend_cap_le: "unat pend_len \<le> unat pending_cap"
    and budget0:
      "encode_window_section_budget src_bytes tgt_bytes
        data_cap inst_cap addr_cap spec_st"
    and abs: "enc_cache_abs s (enc_cache spec_st)"
    and cwf: "enc_cache_wf (enc_cache spec_st)"
    using rel by (simp_all add: encode_window_loop_budget_rel_def)
  have data_slack:
    "unat (sections_t_C.data_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat data_cap"
    using rel unfolding encode_window_loop_budget_rel_def by blast
  have inst_slack:
    "unat (sections_t_C.inst_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat inst_cap"
    using rel unfolding encode_window_loop_budget_rel_def by blast
  have dp_len0: "length (enc_data spec_st) = unat (sections_t_C.data_pos_C sec)"
    and ip_len0: "length (enc_inst spec_st) = unat (sections_t_C.inst_pos_C sec)"
    and ap_len0: "length (enc_addr spec_st) = unat (sections_t_C.addr_pos_C sec)"
    using enc_sections_state_rel_lengths[OF sections_rel] by simp_all
  \<comment> \<open>--- match facts ---\<close>
  have tp_nat_lt: "unat tp < unat tgt_len"
    using tp_lt by (simp add: word_less_nat_alt)
  have tp_le_w: "tp \<le> tgt_len" using tp_lt by simp
  have copy_ge: "(4 :: 32 word) \<le> ?ml"
    using match_len by (simp add: min_match_def)
  have copy_ge_nat: "4 \<le> unat ?ml"
    using copy_ge by (simp add: word_le_nat_alt)
  have len_nz: "unat ?ml \<noteq> 0" using copy_ge_nat by simp
  have match_valid0:
    "match_valid src_bytes tgt_bytes (unat tp) (unat ?mp) (unat ?ml)"
    using match_rel match tp_le_w
    unfolding encode_window_match_rel_def by blast
  let ?best = "find_best_match_spec src_bytes tgt_bytes (unat tp) ?idx"
  have m_eq0: "m =
      (let best = find_best_match_spec src_bytes tgt_bytes (unat tp) ?idx
       in match_t_C (of_nat (em_pos best)) (of_nat (em_len best)))"
    using match_rel match tp_le_w
    unfolding encode_window_match_rel_def by blast
  have m_eq: "m = match_t_C (of_nat (em_pos ?best)) (of_nat (em_len ?best))"
    using m_eq0 by (simp add: Let_def)
  have not_short: "\<not> em_len ?best < min_match"
  proof
    assume short: "em_len ?best < min_match"
    have "unat ?ml = em_len ?best"
      using m_eq short by (simp add: min_match_def unat_of_nat_eq)
    thus False using copy_ge_nat short by (simp add: min_match_def)
  qed
  have min_le: "min_match \<le> em_len ?best" using not_short by simp
  have sound:
    "em_pos ?best + em_len ?best \<le> length src_bytes \<and>
     unat tp + em_len ?best \<le> length tgt_bytes \<and>
     (\<forall>k < em_len ?best.
        src_bytes ! (em_pos ?best + k) = tgt_bytes ! (unat tp + k))"
    by (rule find_best_match_spec_sound[OF refl min_le])
  have best_len32: "em_len ?best < 2 ^ 32"
  proof -
    have "em_len ?best \<le> unat tp + em_len ?best" by simp
    also have "... \<le> length tgt_bytes" using sound by simp
    also have "... = unat tgt_len" using tgt_len_eq by simp
    also have "... < 2 ^ 32" using unat_lt2p[of tgt_len] by simp
    finally show ?thesis .
  qed
  have best_pos32: "em_pos ?best < 2 ^ 32"
  proof -
    have "em_pos ?best \<le> em_pos ?best + em_len ?best" by simp
    also have "... \<le> length src_bytes" using sound by simp
    also have "... = unat src_len" using src_len_eq by simp
    also have "... < 2 ^ 32" using unat_lt2p[of src_len] by simp
    finally show ?thesis .
  qed
  have c_len: "unat ?ml = em_len ?best"
    using m_eq best_len32 by (simp add: unat_of_nat_eq)
  have c_pos: "unat ?mp = em_pos ?best"
    using m_eq best_pos32 by (simp add: unat_of_nat_eq)
  have tp_len_room_nat: "unat tp + unat ?ml \<le> unat tgt_len"
    using match_validD(2)[OF match_valid0 len_nz] tgt_len_eq by simp
  have pos_len_room_nat: "unat ?mp + unat ?ml \<le> length src_bytes"
    using match_validD(1)[OF match_valid0 len_nz] by simp
  have tp_len_no_overflow: "unat tp + unat ?ml < 2 ^ 32"
    using tp_len_room_nat unat_lt2p[of tgt_len] by simp
  have tp_len_unat: "unat (tp + ?ml) = unat tp + unat ?ml"
    by (rule unat_word_add_no_overflow[OF tp_len_no_overflow])
  have tp_len_le_nat: "unat (tp + ?ml) \<le> unat tgt_len"
    using tp_len_room_nat tp_len_unat by simp
  have measure_progress:
    "unat tgt_len - unat (tp + ?ml) < unat tgt_len - unat tp"
    using tp_len_le_nat tp_len_unat copy_ge_nat tp_nat_lt by linarith
  \<comment> \<open>--- shape of the fused spec state ---\<close>
  define cn where "cn = enc_tp spec_st' - enc_tp spec_st"
  have cn_facts: "enc_tp spec_st + 4 \<le> enc_tp spec_st'"
      "enc_tp spec_st' \<le> enc_tp spec_st + unat ?ml"
    using try_emit_add_copy_spec_Some_facts[OF fused] by simp_all
  have tp'_eq: "enc_tp spec_st' = enc_tp spec_st + cn"
    using cn_facts cn_def by simp
  have cn_ge4: "4 \<le> cn" using cn_facts cn_def by simp
  have cn_le_len: "cn \<le> unat ?ml" using cn_facts cn_def by simp
  have pending': "enc_pending spec_st' = []"
    and flushed':
      "enc_flushed spec_st' =
       enc_flushed spec_st + length (enc_pending spec_st) +
         (enc_tp spec_st' - enc_tp spec_st)"
    and data'_len:
      "length (enc_data spec_st') =
       length (enc_data spec_st) + length (enc_pending spec_st)"
    and inst'_len:
      "length (enc_inst spec_st') = length (enc_inst spec_st) + 1"
    using try_emit_add_copy_spec_Some_shape[OF fused] by simp_all
  have flushed'_eq: "enc_flushed spec_st' = enc_tp spec_st'"
    using flushed' flushed_inv cn_facts(1) by linarith
  have pend_ge_nat: "1 \<le> unat pend_len"
    using fused pending_len
    by (auto simp: try_emit_add_copy_spec_def Let_def min_match_def
             split: option.splits prod.splits if_splits)
  \<comment> \<open>--- the post-step spec state and its budget ---\<close>
  define spec2 where "spec2 =
    (if cn < unat ?ml
     then emit_copy_spec (length src_bytes) (unat ?mp + cn)
            (unat ?ml - cn) spec_st'
     else spec_st')"
  have step_eq: "spec2 = encode_window_full_step src_bytes tgt_bytes ?idx spec_st"
    using not_short fused c_pos c_len tp_eq cn_def
    by (simp add: encode_window_full_step_def Let_def spec2_def)
  have tp_spec_lt: "enc_tp spec_st < length tgt_bytes"
    using tp_eq tp_nat_lt tgt_len_eq by simp
  have not_short':
    "\<not> em_len (find_best_match_spec src_bytes tgt_bytes (enc_tp spec_st)
        ?idx) < min_match"
    using not_short tp_eq by simp
  have budget2:
    "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap spec2"
    by (rule encode_window_section_budget_match_step[
          OF budget0 tp_spec_lt not_short' step_eq])
  have caps2:
    "length (enc_data spec2) \<le> unat data_cap \<and>
     length (enc_inst spec2) \<le> unat inst_cap \<and>
     length (enc_addr spec2) \<le> unat addr_cap"
  proof -
    let ?fin = "encode_window_final_spec_state src_bytes tgt_bytes"
    have pfx: "length (enc_data spec2) \<le> length (enc_data ?fin) \<and>
               length (enc_inst spec2) \<le> length (enc_inst ?fin) \<and>
               length (enc_addr spec2) \<le> length (enc_addr ?fin)"
      using budget2
      by (simp add: encode_window_section_budget_def
          encode_window_section_prefix_budget_def)
    have fin: "length (enc_data ?fin) \<le> unat data_cap \<and>
               length (enc_inst ?fin) \<le> unat inst_cap \<and>
               length (enc_addr ?fin) \<le> unat addr_cap"
      using budget2
      by (simp add: encode_window_section_budget_def
          encoder_final_section_caps_ok_def)
    show ?thesis using pfx fin by linarith
  qed
  have mono12:
    "length (enc_data spec_st') \<le> length (enc_data spec2) \<and>
     length (enc_inst spec_st') \<le> length (enc_inst spec2) \<and>
     length (enc_addr spec_st') \<le> length (enc_addr spec2)"
    using emit_copy_spec_sections_mono[of spec_st' "length src_bytes"]
    by (auto simp: spec2_def)
  have data_room': "length (enc_data spec_st') \<le> unat data_cap"
    and inst_room': "length (enc_inst spec_st') \<le> unat inst_cap"
    and addr_room': "length (enc_addr spec_st') \<le> unat addr_cap"
    using mono12 caps2 by linarith+
  \<comment> \<open>--- best mode and exact address encoding for the fused emit ---\<close>
  obtain bm where bm: "best_mode' ?mp (src_len + tp) s = Some bm"
    by (rule best_mode'_some[OF abs cwf])
  have src_tp_no: "unat src_len + unat tp < 2 ^ 32"
    using src_len_eq tgt_len_eq src_tgt_bound tp_nat_lt by linarith
  have here_eq: "unat (src_len + tp) = length src_bytes + enc_tp spec_st"
    using src_len_eq tp_eq src_tp_no
    by (simp add: unat_word_ariths)
  have addr_exact:
    "encode_address (enc_cache spec_st) (unat ?mp)
       (length src_bytes + enc_tp spec_st) =
     (unat (mode_t_C.mode_C bm),
      enc_best_bytes (mode_t_C.mode_C bm) (mode_t_C.arg_C bm),
      cache_update (enc_cache spec_st) (unat ?mp))"
    using best_mode'_encode_address_exact[OF abs cwf bm] here_eq by simp
  \<comment> \<open>--- keystone for the fused emit ---\<close>
  have KS:
    "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
        pending pend_len ?mp (src_len + tp) ?ml \<bullet> s
      \<lbrace> \<lambda>r t. \<exists>f.
          r = Result f \<and>
          fused_t_C.fused_C f \<noteq> 0 \<and>
          unat (fused_t_C.fused_C f) = enc_tp spec_st' - enc_tp spec_st \<and>
          sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK \<and>
          sections_t_C.data_pos_C (fused_t_C.s_C f) =
            sections_t_C.data_pos_C sec + pend_len \<and>
          enc_sections_state_rel t data inst addr
            (fused_t_C.s_C f) spec_st' \<and>
          enc_cache_abs t (enc_cache spec_st') \<and>
          enc_cache_wf (enc_cache spec_st') \<and>
          heap_bytes t src (unat src_len) = heap_bytes s src (unat src_len) \<and>
          heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    by (rule try_emit_add_copy'_state_rel_cache_frame_from_loop[
          OF buffers sections_rel abs cwf pending_heap pending_len
             pend_cap_le bm addr_exact fused sec_ok
             data_room' inst_room' addr_room'])
  \<comment> \<open>--- the continuation of the C match branch after the fused try ---\<close>
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
                      (match_t_C.pos_C m + fused_t_C.fused_C f)
                      (src_len + (tp + fused_t_C.fused_C f))
                      (match_t_C.len_C m - fused_t_C.fused_C f));
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
    "\<And>f t. \<lbrakk>
        fused_t_C.fused_C f \<noteq> 0;
        unat (fused_t_C.fused_C f) = enc_tp spec_st' - enc_tp spec_st;
        sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK;
        sections_t_C.data_pos_C (fused_t_C.s_C f) =
          sections_t_C.data_pos_C sec + pend_len;
        enc_sections_state_rel t data inst addr (fused_t_C.s_C f) spec_st';
        enc_cache_abs t (enc_cache spec_st');
        enc_cache_wf (enc_cache spec_st');
        heap_bytes t src (unat src_len) = heap_bytes s src (unat src_len);
        heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len);
        heap_typing t = heap_typing s \<rbrakk> \<Longrightarrow>
        ?cont f \<bullet> t \<lbrace> ?Q \<rbrace>"
  proof -
    fix f t
    assume fz: "fused_t_C.fused_C f \<noteq> 0"
      and fcn: "unat (fused_t_C.fused_C f) =
          enc_tp spec_st' - enc_tp spec_st"
      and err_f: "sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK"
      and dpos_f: "sections_t_C.data_pos_C (fused_t_C.s_C f) =
          sections_t_C.data_pos_C sec + pend_len"
      and srel_f: "enc_sections_state_rel t data inst addr
          (fused_t_C.s_C f) spec_st'"
      and cabs_f: "enc_cache_abs t (enc_cache spec_st')"
      and cwf_f: "enc_cache_wf (enc_cache spec_st')"
      and src_fr: "heap_bytes t src (unat src_len) =
          heap_bytes s src (unat src_len)"
      and tgt_fr: "heap_bytes t tgt (unat tgt_len) =
          heap_bytes s tgt (unat tgt_len)"
      and typing_f: "heap_typing t = heap_typing s"
    have fcn': "unat (fused_t_C.fused_C f) = cn"
      using fcn cn_def by simp
    have src_heap_t: "heap_bytes t src (unat src_len) = src_bytes"
      using src_fr src_heap by simp
    have tgt_heap_t: "heap_bytes t tgt (unat tgt_len) = tgt_bytes"
      using tgt_fr tgt_heap by simp
    have buffers_t:
      "encode_window_loop_buffers_ok t src src_len tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
      by (rule encode_window_loop_buffers_ok_heap_typing[OF buffers typing_f])
    have dp'_len: "length (enc_data spec_st') =
        unat (sections_t_C.data_pos_C (fused_t_C.s_C f))"
      and ip'_len: "length (enc_inst spec_st') =
        unat (sections_t_C.inst_pos_C (fused_t_C.s_C f))"
      and ap'_len: "length (enc_addr spec_st') =
        unat (sections_t_C.addr_pos_C (fused_t_C.s_C f))"
      using enc_sections_state_rel_lengths[OF srel_f] by simp_all
    show "?cont f \<bullet> t \<lbrace> ?Q \<rbrace>"
    proof (cases "cn < unat ?ml")
      case rem: True
      have len7: "7 \<le> unat ?ml"
        using try_emit_add_copy_spec_Some_partial_six[OF fused] rem cn_def
        by simp
      have fused_lt: "fused_t_C.fused_C f < ?ml"
        using fcn' rem by (simp add: word_less_nat_alt)
      have fused_le_w: "fused_t_C.fused_C f \<le> ?ml"
        using fused_lt by simp
      have rem_unat: "unat (?ml - fused_t_C.fused_C f) = unat ?ml - cn"
        using fcn' fused_le_w by (simp add: unat_sub)
      have pos_cn_no: "unat ?mp + cn < 2 ^ 32"
      proof -
        have "unat ?mp + cn \<le> length src_bytes"
          using pos_len_room_nat cn_le_len by linarith
        also have "... = unat src_len" using src_len_eq by simp
        also have "... < 2 ^ 32" using unat_lt2p[of src_len] by simp
        finally show ?thesis .
      qed
      have pos_arith: "unat (?mp + fused_t_C.fused_C f) = unat ?mp + cn"
        using fcn' pos_cn_no by (simp add: unat_word_ariths)
      have spec2_rem: "spec2 =
          emit_copy_spec (length src_bytes) (unat ?mp + cn)
            (unat ?ml - cn) spec_st'"
        using rem by (simp add: spec2_def)
      \<comment> \<open>remainder copy keystone\<close>
      obtain bm2 where bm2:
        "best_mode' (?mp + fused_t_C.fused_C f)
           (src_len + (tp + fused_t_C.fused_C f)) t = Some bm2"
        by (rule best_mode'_some[OF cabs_f cwf_f])
      have here2_no: "unat src_len + unat tp + cn < 2 ^ 32"
        using src_len_eq tgt_len_eq src_tgt_bound tp_len_room_nat cn_le_len
        by linarith
      have tp_cn_no: "unat tp + cn < 2 ^ 32"
        using here2_no by linarith
      have here2_eq:
        "unat (src_len + (tp + fused_t_C.fused_C f)) =
         length src_bytes + enc_flushed spec_st'"
        using src_len_eq flushed'_eq tp'_eq tp_eq fcn' here2_no tp_cn_no
        by (simp add: unat_word_ariths)
      have addr_exact2:
        "encode_address (enc_cache spec_st')
           (unat (?mp + fused_t_C.fused_C f))
           (length src_bytes + enc_flushed spec_st') =
         (unat (mode_t_C.mode_C bm2),
          enc_best_bytes (mode_t_C.mode_C bm2) (mode_t_C.arg_C bm2),
          cache_update (enc_cache spec_st')
            (unat (?mp + fused_t_C.fused_C f)))"
        using best_mode'_encode_address_exact[OF cabs_f cwf_f bm2] here2_eq
        by simp
      have spec2_ks: "spec2 =
          emit_copy_spec (length src_bytes)
            (unat (?mp + fused_t_C.fused_C f))
            (unat (?ml - fused_t_C.fused_C f)) spec_st'"
        using spec2_rem pos_arith rem_unat by simp
      have dpos_le_f:
        "unat (sections_t_C.data_pos_C (fused_t_C.s_C f)) \<le> unat data_cap"
        using dp'_len data_room' by simp
      have inst_room2:
        "length (enc_inst (emit_copy_spec (length src_bytes)
           (unat (?mp + fused_t_C.fused_C f))
           (unat (?ml - fused_t_C.fused_C f)) spec_st')) \<le> unat inst_cap"
        using spec2_ks caps2 by simp
      have addr_room2:
        "length (enc_addr (emit_copy_spec (length src_bytes)
           (unat (?mp + fused_t_C.fused_C f))
           (unat (?ml - fused_t_C.fused_C f)) spec_st')) \<le> unat addr_cap"
        using spec2_ks caps2 by simp
      have EK:
        "emit_copy' (fused_t_C.s_C f) inst inst_cap addr addr_cap
           (?mp + fused_t_C.fused_C f)
           (src_len + (tp + fused_t_C.fused_C f))
           (?ml - fused_t_C.fused_C f) \<bullet> t
         \<lbrace> \<lambda>r u. \<exists>sec2.
              r = Result sec2 \<and>
              sections_t_C.err_C sec2 = ENC_OK \<and>
              sections_t_C.data_pos_C sec2 =
                sections_t_C.data_pos_C (fused_t_C.s_C f) \<and>
              unat (sections_t_C.inst_pos_C sec2) \<le> unat inst_cap \<and>
              unat (sections_t_C.addr_pos_C sec2) \<le> unat addr_cap \<and>
              enc_sections_state_rel u data inst addr sec2
                (emit_copy_spec (length src_bytes)
                  (unat (?mp + fused_t_C.fused_C f))
                  (unat (?ml - fused_t_C.fused_C f)) spec_st') \<and>
              enc_cache_abs u
                (cache_update (enc_cache spec_st')
                  (unat (?mp + fused_t_C.fused_C f))) \<and>
              enc_cache_wf
                (cache_update (enc_cache spec_st')
                  (unat (?mp + fused_t_C.fused_C f))) \<and>
              heap_bytes u src (unat src_len) =
                heap_bytes t src (unat src_len) \<and>
              heap_bytes u tgt (unat tgt_len) =
                heap_bytes t tgt (unat tgt_len) \<and>
              heap_typing u = heap_typing t \<rbrace>"
        by (rule emit_copy'_state_rel_cache_frame_from_loop[
              OF buffers_t srel_f cabs_f cwf_f bm2 addr_exact2 err_f
                 dpos_le_f inst_room2 addr_room2])
      have cache2_eq:
        "enc_cache spec2 =
         cache_update (enc_cache spec_st')
           (unat (?mp + fused_t_C.fused_C f))"
        using emit_copy_spec_cache_of_encode_address[OF addr_exact2]
          spec2_ks
        by simp
      have tp2_eq: "enc_tp spec2 = unat (tp + ?ml)"
        using spec2_rem emit_copy_spec_components(2)[of "length src_bytes"]
          tp'_eq tp_eq cn_le_len tp_len_unat
        by simp
      have flushed2_eq: "enc_flushed spec2 = enc_tp spec2"
        using spec2_rem
          emit_copy_spec_components(2,3)[of "length src_bytes"]
          flushed'_eq
        by simp
      have pending2: "enc_pending spec2 = []"
        using spec2_rem emit_copy_spec_components(1)[of "length src_bytes"]
          pending'
        by simp
      have data2_len:
        "length (enc_data spec2) =
         unat (sections_t_C.data_pos_C sec) + unat pend_len"
        using spec2_rem emit_copy_spec_components(4)[of "length src_bytes"]
          data'_len dp_len0 pending_len
        by simp
      have inst2_len_ub:
        "length (enc_inst spec2) \<le>
         unat (sections_t_C.inst_pos_C sec) + 7"
      proof -
        have l32: "unat ?ml - cn < 2 ^ 32"
          using unat_lt2p[of ?ml] by simp
        show ?thesis
          using spec2_rem emit_copy_spec_inst_growth[OF l32,
              of "length src_bytes" "unat ?mp + cn" spec_st']
            inst'_len ip_len0
          by simp
      qed
      have tp_progress2: "enc_tp spec_st < enc_tp spec2"
        using tp2_eq tp_eq tp_len_unat copy_ge_nat by simp
      \<comment> \<open>budget invariant after the remainder copy\<close>
      have rel_after:
        "\<And>u sec2. \<lbrakk>
            sections_t_C.err_C sec2 = ENC_OK;
            sections_t_C.data_pos_C sec2 =
              sections_t_C.data_pos_C (fused_t_C.s_C f);
            enc_sections_state_rel u data inst addr sec2 spec2;
            enc_cache_abs u (enc_cache spec2);
            enc_cache_wf (enc_cache spec2);
            heap_bytes u src (unat src_len) = src_bytes;
            heap_bytes u tgt (unat tgt_len) = tgt_bytes \<rbrakk> \<Longrightarrow>
          encode_window_loop_budget_rel u src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec2 (tp + ?ml) 0 src_bytes tgt_bytes spec2"
      proof -
        fix u sec2
        assume ok2: "sections_t_C.err_C sec2 = ENC_OK"
          and dpos2: "sections_t_C.data_pos_C sec2 =
              sections_t_C.data_pos_C (fused_t_C.s_C f)"
          and srel2: "enc_sections_state_rel u data inst addr sec2 spec2"
          and cabs2: "enc_cache_abs u (enc_cache spec2)"
          and cwf2: "enc_cache_wf (enc_cache spec2)"
          and srcu: "heap_bytes u src (unat src_len) = src_bytes"
          and tgtu: "heap_bytes u tgt (unat tgt_len) = tgt_bytes"
        have dp2_len: "length (enc_data spec2) =
            unat (sections_t_C.data_pos_C sec2)"
          and ip2_len: "length (enc_inst spec2) =
            unat (sections_t_C.inst_pos_C sec2)"
          and ap2_len: "length (enc_addr spec2) =
            unat (sections_t_C.addr_pos_C sec2)"
          using enc_sections_state_rel_lengths[OF srel2] by simp_all
        have pending_u: "heap_bytes_word u pending 0 0 = enc_pending spec2"
          using pending2 by (simp add: heap_bytes_word_def)
        have data_slack2:
          "unat (sections_t_C.data_pos_C sec2) + unat (0 :: 32 word) +
             (unat tgt_len - unat (tp + ?ml)) + 64 \<le> unat data_cap"
          using dp2_len data2_len data_slack tp_len_unat tp_len_le_nat
          by simp
        have inst_slack2:
          "unat (sections_t_C.inst_pos_C sec2) + unat (0 :: 32 word) +
             (unat tgt_len - unat (tp + ?ml)) + 64 \<le> unat inst_cap"
        proof -
          have "unat (sections_t_C.inst_pos_C sec2) \<le>
              unat (sections_t_C.inst_pos_C sec) + 7"
            using ip2_len inst2_len_ub by simp
          moreover have "unat (tp + ?ml) = unat tp + unat ?ml"
            by (rule tp_len_unat)
          moreover have "unat (0 :: 32 word) = 0" by simp
          ultimately show ?thesis
            using inst_slack len7 pend_ge_nat tp_len_le_nat by linarith
        qed
        show "encode_window_loop_budget_rel u src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec2 (tp + ?ml) 0 src_bytes tgt_bytes spec2"
          using srcu tgtu src_len_eq tgt_len_eq pending_u pending2
            tp2_eq flushed2_eq srel2 ok2 tp_len_le_nat
            dp2_len ip2_len ap2_len caps2 data_slack2 inst_slack2
            budget2 cabs2 cwf2
          by (auto simp: encode_window_loop_budget_rel_def)
      qed
      have EK_lifted:
        "liftE (emit_copy' (fused_t_C.s_C f) inst inst_cap addr addr_cap
            (?mp + fused_t_C.fused_C f)
            (src_len + (tp + fused_t_C.fused_C f))
            (?ml - fused_t_C.fused_C f)) \<bullet> t
         \<lbrace> \<lambda>r u. \<exists>sec2. r = Result sec2 \<and>
              sections_t_C.err_C sec2 = 0 \<and>
              ?Q (Result (0, sec2, tp + ?ml)) u \<rbrace>"
        apply (rule runs_to_liftE)
        apply (rule runs_to_weaken[OF EK])
        apply clarsimp
        subgoal for secx u
          apply (rule exI[where x = spec2])
          using rel_after[of secx u] cache2_eq spec2_ks src_heap_t
            tgt_heap_t tp_progress2 measure_progress dpos_f
          by auto
        done
      show "?cont f \<bullet> t \<lbrace> ?Q \<rbrace>"
        apply (simp add: err_f fz fused_lt)
        apply (rule runs_to_bind)
        apply (rule runs_to_bind)
        apply (rule runs_to_weaken[OF EK_lifted])
        by (auto simp: runs_to_bind_iff runs_to_condition_iff)
    next
      case norem: False
      have cn_eq_len: "cn = unat ?ml"
        using norem cn_le_len by simp
      have feq: "fused_t_C.fused_C f = ?ml"
        using fcn' cn_eq_len by (metis word_unat.Rep_eqD)
      have fused_not_lt: "\<not> fused_t_C.fused_C f < ?ml"
        using feq by simp
      have spec2_eq: "spec2 = spec_st'"
        using norem by (simp add: spec2_def)
      have tp2_eq: "enc_tp spec_st' = unat (tp + ?ml)"
        using tp'_eq tp_eq cn_eq_len tp_len_unat by simp
      have tp_progress2: "enc_tp spec_st < enc_tp spec_st'"
        using tp'_eq cn_ge4 by simp
      have pending_t: "heap_bytes_word t pending 0 0 = enc_pending spec_st'"
        using pending' by (simp add: heap_bytes_word_def)
      have data'_len_c:
        "length (enc_data spec_st') =
         unat (sections_t_C.data_pos_C sec) + unat pend_len"
        using data'_len dp_len0 pending_len by simp
      have data_slack':
        "unat (sections_t_C.data_pos_C (fused_t_C.s_C f)) +
           unat (0 :: 32 word) +
           (unat tgt_len - unat (tp + ?ml)) + 64 \<le> unat data_cap"
        using dp'_len data'_len_c data_slack tp_len_unat tp_len_le_nat
        by simp
      have inst_slack':
        "unat (sections_t_C.inst_pos_C (fused_t_C.s_C f)) +
           unat (0 :: 32 word) +
           (unat tgt_len - unat (tp + ?ml)) + 64 \<le> unat inst_cap"
      proof -
        have "unat (sections_t_C.inst_pos_C (fused_t_C.s_C f)) =
            unat (sections_t_C.inst_pos_C sec) + 1"
          using ip'_len inst'_len ip_len0 by simp
        moreover have "unat (tp + ?ml) = unat tp + unat ?ml"
          by (rule tp_len_unat)
        moreover have "unat (0 :: 32 word) = 0" by simp
        ultimately show ?thesis
          using inst_slack pend_ge_nat copy_ge_nat tp_len_le_nat by linarith
      qed
      have rel_after:
        "encode_window_loop_budget_rel t src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            (fused_t_C.s_C f) (tp + ?ml) 0 src_bytes tgt_bytes spec_st'"
        using src_heap_t tgt_heap_t src_len_eq tgt_len_eq pending_t pending'
          tp2_eq flushed'_eq srel_f err_f tp_len_le_nat
          dp'_len ip'_len ap'_len data_room' inst_room' addr_room'
          data_slack' inst_slack'
          budget2 spec2_eq cabs_f cwf_f
        by (auto simp: encode_window_loop_budget_rel_def)
      show "?cont f \<bullet> t \<lbrace> ?Q \<rbrace>"
        apply (simp add: err_f fz fused_not_lt feq)
        using rel_after tp_progress2 measure_progress spec2_eq budget2
        by (auto simp: runs_to_bind_iff runs_to_condition_iff)
    qed
  qed
  \<comment> \<open>--- assemble the branch ---\<close>
  have ks_lifted:
    "liftE (try_emit_add_copy' sec data data_cap inst inst_cap
        addr addr_cap pending pend_len ?mp (src_len + tp) ?ml) \<bullet> s
     \<lbrace> \<lambda>r t. \<exists>f.
          r = Result f \<and>
          fused_t_C.fused_C f \<noteq> 0 \<and>
          unat (fused_t_C.fused_C f) = enc_tp spec_st' - enc_tp spec_st \<and>
          sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK \<and>
          sections_t_C.data_pos_C (fused_t_C.s_C f) =
            sections_t_C.data_pos_C sec + pend_len \<and>
          enc_sections_state_rel t data inst addr
            (fused_t_C.s_C f) spec_st' \<and>
          enc_cache_abs t (enc_cache spec_st') \<and>
          enc_cache_wf (enc_cache spec_st') \<and>
          heap_bytes t src (unat src_len) = heap_bytes s src (unat src_len) \<and>
          heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len) \<and>
          heap_typing t = heap_typing s \<rbrace>"
    apply (rule runs_to_liftE)
    apply (rule runs_to_weaken[OF KS])
    by auto
  have ks_for_bind:
    "liftE (try_emit_add_copy' sec data data_cap inst inst_cap
        addr addr_cap pending pend_len ?mp (src_len + tp) ?ml) \<bullet> s
     \<lbrace> \<lambda>r t.
          (\<forall>v. r = Result v \<longrightarrow> ?cont v \<bullet> t \<lbrace> ?Q \<rbrace>) \<and>
          (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> ?Q (Exception e) t) \<rbrace>"
  proof (rule runs_to_weaken[OF ks_lifted])
    fix r t
    assume "\<exists>f.
          r = Result f \<and>
          fused_t_C.fused_C f \<noteq> 0 \<and>
          unat (fused_t_C.fused_C f) = enc_tp spec_st' - enc_tp spec_st \<and>
          sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK \<and>
          sections_t_C.data_pos_C (fused_t_C.s_C f) =
            sections_t_C.data_pos_C sec + pend_len \<and>
          enc_sections_state_rel t data inst addr
            (fused_t_C.s_C f) spec_st' \<and>
          enc_cache_abs t (enc_cache spec_st') \<and>
          enc_cache_wf (enc_cache spec_st') \<and>
          heap_bytes t src (unat src_len) = heap_bytes s src (unat src_len) \<and>
          heap_bytes t tgt (unat tgt_len) = heap_bytes s tgt (unat tgt_len) \<and>
          heap_typing t = heap_typing s"
    then obtain f where r_def: "r = Result f"
      and P1: "fused_t_C.fused_C f \<noteq> 0"
      and P2: "unat (fused_t_C.fused_C f) =
          enc_tp spec_st' - enc_tp spec_st"
      and P3: "sections_t_C.err_C (fused_t_C.s_C f) = ENC_OK"
      and P4: "sections_t_C.data_pos_C (fused_t_C.s_C f) =
          sections_t_C.data_pos_C sec + pend_len"
      and P5: "enc_sections_state_rel t data inst addr
          (fused_t_C.s_C f) spec_st'"
      and P6: "enc_cache_abs t (enc_cache spec_st')"
      and P7: "enc_cache_wf (enc_cache spec_st')"
      and P8: "heap_bytes t src (unat src_len) =
          heap_bytes s src (unat src_len)"
      and P9: "heap_bytes t tgt (unat tgt_len) =
          heap_bytes s tgt (unat tgt_len)"
      and P10: "heap_typing t = heap_typing s"
      by blast
    have cont_f: "?cont f \<bullet> t \<lbrace> ?Q \<rbrace>"
      by (rule fused_cont[OF P1 P2 P3 P4 P5 P6 P7 P8 P9 P10])
    show "(\<forall>v. r = Result v \<longrightarrow> ?cont v \<bullet> t \<lbrace> ?Q \<rbrace>) \<and>
          (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> ?Q (Exception e) t)"
      using r_def cont_f by auto
  qed
  have branch_unfold:
    "encode_window_c_match_branch src_len
       data data_cap inst inst_cap addr addr_cap
       pending pend_len sec tp m =
     bind (liftE
       (try_emit_add_copy' sec data data_cap inst inst_cap
         addr addr_cap pending pend_len ?mp (src_len + tp) ?ml)) ?cont"
    by (simp add: encode_window_c_match_branch_def)
  show ?thesis
    apply (subst branch_unfold)
    apply (rule runs_to_bind[OF ks_for_bind])
    done
qed

lemma flush_pending'_loop_from_final_fits_framed:
  fixes s :: lifted_globals
    and src tgt data inst addr pending :: "8 word ptr"
    and src_len tgt_len data_cap inst_cap addr_cap pending_cap pend_len :: "32 word"
  assumes buffers:
      "encode_window_loop_buffers_ok s src src_len tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
    and rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and abs: "enc_cache_abs s c"
    and cache_wf: "enc_cache_wf c"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and pending_eq:
      "enc_pending spec_st = heap_bytes_word s pending 0 pend_len"
    and pend_len_le: "unat pend_len \<le> unat pending_cap"
    and final_data_room64:
      "length (enc_data (flush_pending_spec sl spec_st)) + 64 \<le> unat data_cap"
    and final_inst_room64:
      "length (enc_inst (flush_pending_spec sl spec_st)) + 64 \<le> unat inst_cap"
    and final_addr_room:
      "length (enc_addr (flush_pending_spec sl spec_st)) \<le> unat addr_cap"
  shows "flush_pending' sec data data_cap inst inst_cap pending pend_len \<bullet> s
         \<lbrace> \<lambda>r t. \<exists>sec'.
              r = Result sec' \<and>
              enc_sections_state_rel t data inst addr sec'
                (flush_pending_spec sl spec_st) \<and>
              sections_t_C.err_C sec' = ENC_OK \<and>
              heap_bytes_word t src 0 src_len =
                heap_bytes_word s src 0 src_len \<and>
              heap_bytes_word t tgt 0 tgt_len =
                heap_bytes_word s tgt 0 tgt_len \<and>
              enc_cache_abs t c \<and>
              heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?pending_bytes = "heap_bytes_word s pending 0 pend_len"
  let ?final_st = "flush_pending_spec sl spec_st"
  let ?P = "\<lambda>u. heap_bytes_word u src 0 src_len =
                  heap_bytes_word s src 0 src_len \<and>
                heap_bytes_word u tgt 0 tgt_len =
                  heap_bytes_word s tgt 0 tgt_len \<and>
                enc_cache_abs u c"
  have P0: "?P s" using abs by simp
  have inst_src0: "bufs_disjoint inst (unat inst_cap) src (unat src_len)"
    and inst_tgt0: "bufs_disjoint inst (unat inst_cap) tgt (unat tgt_len)"
    and data_src0: "bufs_disjoint data (unat data_cap) src (unat src_len)"
    and data_tgt0: "bufs_disjoint data (unat data_cap) tgt (unat tgt_len)"
    using buffers by (auto simp: encode_window_loop_buffers_ok_def)
  have src_inst_disj: "bufs_disjoint src (unat src_len) inst (unat inst_cap)"
    by (rule bufs_disjoint_sym[THEN iffD1, OF inst_src0])
  have tgt_inst_disj: "bufs_disjoint tgt (unat tgt_len) inst (unat inst_cap)"
    by (rule bufs_disjoint_sym[THEN iffD1, OF inst_tgt0])
  have src_data_disj: "bufs_disjoint src (unat src_len) data (unat data_cap)"
    by (rule bufs_disjoint_sym[THEN iffD1, OF data_src0])
  have tgt_data_disj: "bufs_disjoint tgt (unat tgt_len) data (unat data_cap)"
    by (rule bufs_disjoint_sym[THEN iffD1, OF data_tgt0])
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
        ?P t;
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
	             heap_typing u = heap_typing s \<and>
	             ?P u \<rbrace>"
    proof -
      fix add_start i sec_cur t loop_st
      assume inv:
        "flush_pending_outer_loop_inv (sl) s data inst addr
          pending pend_len spec_st add_start i sec_cur t"
      assume P_t: "?P t"
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
      have src_frame_t:
        "heap_bytes_word t src 0 src_len = heap_bytes_word s src 0 src_len"
        and tgt_frame_t:
        "heap_bytes_word t tgt 0 tgt_len = heap_bytes_word s tgt 0 tgt_len"
        and abs_t: "enc_cache_abs t c"
        using P_t by auto
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
	             heap_typing u = heap_typing s \<and>
	             ?P u \<rbrace>"
      proof (cases "add_start < pend_len")
        case False
	        show ?thesis
	          using False rel_cur typing_t_s sec_cur_ok P_t
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
            cur_addr_le_final final_addr_room by linarith
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
        have add_src_frame:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u src 0 src_len =
                  heap_bytes_word t src 0 src_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t \<rbrace>"
          by (rule emit_add'_loop_buffers_heap_word_cache_frame[
                OF buffers typing_t_s0 abs_t cache_wf sec_cur_ok sz_ge
                   pending_range data_room_add inst_room_add
                   src_inst_disj src_data_disj])
        have add_tgt_frame:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u tgt 0 tgt_len =
                  heap_bytes_word t tgt 0 tgt_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t \<rbrace>"
          by (rule emit_add'_loop_buffers_heap_word_cache_frame[
                OF buffers typing_t_s0 abs_t cache_wf sec_cur_ok sz_ge
                   pending_range data_room_add inst_room_add
                   tgt_inst_disj tgt_data_disj])
        have add_framed:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                ((\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?add_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t) \<and>
                ((\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u src 0 src_len =
                  heap_bytes_word t src 0 src_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t) \<and>
                ((\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u tgt 0 tgt_len =
                  heap_bytes_word t tgt 0 tgt_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t) \<rbrace>"
          using add add_src_frame add_tgt_frame by (simp add: runs_to_conj)
        show ?thesis
          unfolding flush_pending_outer_tail_def
          using add_lt
          apply simp
          apply (rule runs_to_weaken[OF add_framed])
          using typing_t_s frame_t tail_state_eq add_lt add_sections_final
            src_frame_t tgt_frame_t
          apply (auto simp: flush_pending_outer_tail_state_def
              enc_sections_state_rel_def)
          done
      qed
    qed
    have run_pre:
      "\<And>add_start i sec_cur t j b loop_st. \<lbrakk>
        flush_pending_outer_loop_inv (sl) s data inst addr
          pending pend_len spec_st add_start i sec_cur t;
        ?P t;
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
                   pending add_start i j b loop_st) \<and>
               ?P u \<rbrace>"
    proof -
      fix add_start i sec_cur t j b loop_st
      assume inv:
        "flush_pending_outer_loop_inv (sl) s data inst addr
          pending pend_len spec_st add_start i sec_cur t"
      assume P_t: "?P t"
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
      have src_frame_t:
        "heap_bytes_word t src 0 src_len = heap_bytes_word s src 0 src_len"
        and tgt_frame_t:
        "heap_bytes_word t tgt 0 tgt_len = heap_bytes_word s tgt 0 tgt_len"
        and abs_t: "enc_cache_abs t c"
        using P_t by auto
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
                 ?run_state \<and>
               ?P u \<rbrace>"
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
            cur_addr_eq_final final_addr_room by linarith
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
        have run_src_frame:
          "emit_run' sec_cur data data_cap inst inst_cap b (j - i) \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u src 0 src_len =
                  heap_bytes_word t src 0 src_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t \<rbrace>"
          by (rule emit_run'_loop_buffers_heap_word_cache_frame[
                OF buffers typing_t_s0 abs_t cache_wf sec_cur_ok
                   data_room_run inst_room_run
                   src_inst_disj src_data_disj])
        have run_tgt_frame:
          "emit_run' sec_cur data data_cap inst inst_cap b (j - i) \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u tgt 0 tgt_len =
                  heap_bytes_word t tgt 0 tgt_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t \<rbrace>"
          by (rule emit_run'_loop_buffers_heap_word_cache_frame[
                OF buffers typing_t_s0 abs_t cache_wf sec_cur_ok
                   data_room_run inst_room_run
                   tgt_inst_disj tgt_data_disj])
        have run_framed:
          "emit_run' sec_cur data data_cap inst inst_cap b (j - i) \<bullet> t
           \<lbrace> \<lambda>r u.
                ((\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?run_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t) \<and>
                ((\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u src 0 src_len =
                  heap_bytes_word t src 0 src_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t) \<and>
                ((\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u tgt 0 tgt_len =
                  heap_bytes_word t tgt 0 tgt_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t) \<rbrace>"
          using run run_src_frame run_tgt_frame by (simp add: runs_to_conj)
        show ?thesis
          unfolding flush_pending_outer_run_branch_def
          using no_add
          apply simp
          apply (rule runs_to_bind_exception)
           apply (rule runs_to_liftE)
           apply (rule runs_to_weaken[OF run_framed])
          using frame_t typing_t_s src_frame_t tgt_frame_t
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
            cur_addr_eq_final final_addr_room by linarith
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
        have add_src_frame:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u src 0 src_len =
                  heap_bytes_word t src 0 src_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t \<rbrace>"
          by (rule emit_add'_loop_buffers_heap_word_cache_frame[
                OF buffers typing_t_s0 abs_t cache_wf sec_cur_ok sz_ge
                   pending_range add_data_room add_inst_room
                   src_inst_disj src_data_disj])
        have add_tgt_frame:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                (\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u tgt 0 tgt_len =
                  heap_bytes_word t tgt 0 tgt_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t \<rbrace>"
          by (rule emit_add'_loop_buffers_heap_word_cache_frame[
                OF buffers typing_t_s0 abs_t cache_wf sec_cur_ok sz_ge
                   pending_range add_data_room add_inst_room
                   tgt_inst_disj tgt_data_disj])
        have add_framed:
          "emit_add' sec_cur data data_cap inst inst_cap pending add_start
              ?sz \<bullet> t
           \<lbrace> \<lambda>r u.
                ((\<exists>sec'.
                  r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK \<and>
                  enc_sections_state_rel u data inst addr sec'
                    ?add_state) \<and>
                heap_bytes_word u pending 0 pend_len =
                  heap_bytes_word t pending 0 pend_len \<and>
                heap_typing u = heap_typing t) \<and>
                ((\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u src 0 src_len =
                  heap_bytes_word t src 0 src_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t) \<and>
                ((\<exists>sec'. r = Result sec' \<and>
                  sections_t_C.err_C sec' = ENC_OK) \<and>
                heap_bytes_word u tgt 0 tgt_len =
                  heap_bytes_word t tgt 0 tgt_len \<and>
                enc_cache_abs u c \<and>
                enc_cache_wf c \<and>
                heap_typing u = heap_typing t) \<rbrace>"
          using add add_src_frame add_tgt_frame by (simp add: runs_to_conj)
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
	          using final_addr_room add_state_addr_eq_final
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
	                  heap_bytes_word u src 0 src_len =
	                    heap_bytes_word t src 0 src_len \<and>
	                  heap_bytes_word u tgt 0 tgt_len =
	                    heap_bytes_word t tgt 0 tgt_len \<and>
	                  enc_cache_abs u c \<and>
	                  heap_typing u = heap_typing t \<rbrace>"
	          apply (rule runs_to_bind_exception)
	           apply (rule runs_to_liftE)
	           apply (rule runs_to_weaken[OF add_framed])
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
	             have src_frame_u_s:
	               "heap_bytes_word u src 0 src_len =
	                heap_bytes_word s src 0 src_len"
	               using add_post src_frame_t by auto
	             have tgt_frame_u_s:
	               "heap_bytes_word u tgt 0 tgt_len =
	                heap_bytes_word s tgt 0 tgt_len"
	               using add_post tgt_frame_t by auto
	             have abs_u: "enc_cache_abs u c"
	               using add_post by auto
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
	             have run_src_frame2:
	               "emit_run' sec_add data data_cap inst inst_cap b (j - i) \<bullet> u
	                \<lbrace> \<lambda>r v.
	                     (\<exists>sec'. r = Result sec' \<and>
	                       sections_t_C.err_C sec' = ENC_OK) \<and>
	                     heap_bytes_word v src 0 src_len =
	                       heap_bytes_word u src 0 src_len \<and>
	                     enc_cache_abs v c \<and>
	                     enc_cache_wf c \<and>
	                     heap_typing v = heap_typing u \<rbrace>"
	               by (rule emit_run'_loop_buffers_heap_word_cache_frame[
	                     OF buffers typing_u_s0 abs_u cache_wf sec_add_ok
	                        add_run_data_room[OF rel_add]
	                        add_run_inst_room[OF rel_add]
	                        src_inst_disj src_data_disj])
	             have run_tgt_frame2:
	               "emit_run' sec_add data data_cap inst inst_cap b (j - i) \<bullet> u
	                \<lbrace> \<lambda>r v.
	                     (\<exists>sec'. r = Result sec' \<and>
	                       sections_t_C.err_C sec' = ENC_OK) \<and>
	                     heap_bytes_word v tgt 0 tgt_len =
	                       heap_bytes_word u tgt 0 tgt_len \<and>
	                     enc_cache_abs v c \<and>
	                     enc_cache_wf c \<and>
	                     heap_typing v = heap_typing u \<rbrace>"
	               by (rule emit_run'_loop_buffers_heap_word_cache_frame[
	                     OF buffers typing_u_s0 abs_u cache_wf sec_add_ok
	                        add_run_data_room[OF rel_add]
	                        add_run_inst_room[OF rel_add]
	                        tgt_inst_disj tgt_data_disj])
	             have run_framed2:
	               "emit_run' sec_add data data_cap inst inst_cap b (j - i) \<bullet> u
	                \<lbrace> \<lambda>r v.
	                     ((\<exists>sec'.
	                       r = Result sec' \<and>
	                       sections_t_C.err_C sec' = ENC_OK \<and>
	                       enc_sections_state_rel v data inst addr sec'
	                         ?run_state) \<and>
	                     heap_bytes_word v pending 0 pend_len =
	                       heap_bytes_word u pending 0 pend_len \<and>
	                     heap_typing v = heap_typing u) \<and>
	                     ((\<exists>sec'. r = Result sec' \<and>
	                       sections_t_C.err_C sec' = ENC_OK) \<and>
	                     heap_bytes_word v src 0 src_len =
	                       heap_bytes_word u src 0 src_len \<and>
	                     enc_cache_abs v c \<and>
	                     enc_cache_wf c \<and>
	                     heap_typing v = heap_typing u) \<and>
	                     ((\<exists>sec'. r = Result sec' \<and>
	                       sections_t_C.err_C sec' = ENC_OK) \<and>
	                     heap_bytes_word v tgt 0 tgt_len =
	                       heap_bytes_word u tgt 0 tgt_len \<and>
	                     enc_cache_abs v c \<and>
	                     enc_cache_wf c \<and>
	                     heap_typing v = heap_typing u) \<rbrace>"
	               using run run_src_frame2 run_tgt_frame2
	               by (simp add: runs_to_conj)
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
	                         ?run_state \<and>
	                       ?P v \<rbrace>"
	               apply (rule runs_to_bind_exception)
	                apply (rule runs_to_liftE)
	                apply (rule runs_to_weaken[OF run_framed2])
	               using frame_u_s typing_u_s src_frame_u_s tgt_frame_u_s
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
            heap_typing t = heap_typing s \<and>
            ?P t \<rbrace>"
      apply (rule runs_to_weaken[
       OF flush_pending'_enc_sections_state_rel_branch_pre_frame[
         where src_len = "sl" and P = "?P",
         OF rel pending_eq sec_ok pending_valid P0 run_pre tail_pre]])
      apply auto
      done
  show ?thesis
    apply (rule runs_to_weaken[OF flush])
    apply auto
    done
qed

text \<open>Pure facts about a full flush: cache and tp are untouched, flushed
  advances by exactly the pending length, sections grow by at most the
  pending length; plus an emit_copy inst-growth bound by the copy length
  (small opcodes grow by 1, large ones by \<le>6 \<le> len).\<close>

lemma emit_inst_spec_no_copy_cache:
  assumes no_copy: "raw_inst_no_copy i"
  shows "enc_cache (emit_inst_spec sl i st) = enc_cache st"
  using no_copy
  by (cases i) (auto simp: emit_inst_spec_def Let_def split: prod.splits)

lemma emit_insts_spec_no_copy_cache:
  assumes no_copy: "\<forall>i \<in> set insts. raw_inst_no_copy i"
  shows "enc_cache (emit_insts_spec sl insts st) = enc_cache st"
  using no_copy
proof (induction insts arbitrary: st)
  case Nil
  then show ?case by (simp add: emit_insts_spec_def)
next
  case (Cons i insts)
  have step: "emit_insts_spec sl (i # insts) st =
      emit_insts_spec sl insts (emit_inst_spec sl i st)"
    by (simp add: emit_insts_spec_def)
  show ?case
    using Cons emit_inst_spec_no_copy_cache[of i sl st]
    by (simp add: step)
qed

lemma flush_pending_spec_cache:
  "enc_cache (flush_pending_spec sl st) = enc_cache st"
  using emit_insts_spec_no_copy_cache[OF flush_pending_insts_no_copy]
  by (simp add: flush_pending_spec_def)

lemma flush_pending_spec_flushed:
  "enc_flushed (flush_pending_spec sl st) =
   enc_flushed st + length (enc_pending st)"
proof -
  have acc_len: "length (replicate (enc_flushed st) (0 :: byte)) =
      enc_flushed st" by simp
  have "enc_flushed (emit_insts_spec sl
          (flush_pending_insts (enc_pending st)) st) =
        length (exec_inst_list [] (flush_pending_insts (enc_pending st))
          (replicate (enc_flushed st) (0 :: byte)))"
    by (rule emit_insts_spec_enc_flushed_exec[OF acc_len])
  also have "... = enc_flushed st + length (enc_pending st)"
    by (simp add: flush_pending_insts_exec)
  finally show ?thesis
    by (simp add: flush_pending_spec_def)
qed

lemma flush_pending_spec_growth_bounds:
  assumes pending32: "length (enc_pending st) < 2 ^ 32"
  shows "length (enc_data (flush_pending_spec sl st)) \<le>
         length (enc_data st) + length (enc_pending st)"
    and "length (enc_inst (flush_pending_spec sl st)) \<le>
         length (enc_inst st) + length (enc_pending st)"
    and "length (enc_addr (flush_pending_spec sl st)) =
         length (enc_addr st)"
proof -
  have eq: "flush_pending_loop_spec sl (enc_pending st) 0 0 st =
      flush_pending_spec sl st"
    by (rule flush_pending_loop_spec_eq_flush_pending_spec[OF refl])
  show "length (enc_data (flush_pending_spec sl st)) \<le>
         length (enc_data st) + length (enc_pending st)"
    using flush_pending_loop_spec_growth(1)[
        of 0 0 "enc_pending st" sl st] pending32 eq
    by simp
  show "length (enc_inst (flush_pending_spec sl st)) \<le>
         length (enc_inst st) + length (enc_pending st)"
    using flush_pending_loop_spec_growth(2)[
        of 0 0 "enc_pending st" sl st] pending32 eq
    by simp
  show "length (enc_addr (flush_pending_spec sl st)) =
         length (enc_addr st)"
    using flush_pending_loop_spec_growth(3)[
        of 0 0 "enc_pending st" sl st] pending32 eq
    by simp
qed

lemma emit_copy_spec_inst_growth_le_len:
  assumes l_ge: "4 \<le> l" and l_lt: "l < 2 ^ 32"
  shows "length (enc_inst (emit_copy_spec sl a l st)) \<le>
         length (enc_inst st) + l"
proof -
  obtain md ab c' where ea:
    "encode_address (enc_cache st) a (sl + enc_flushed st) = (md, ab, c')"
    by (metis prod_cases3)
  show ?thesis
  proof (cases "l \<le> 18")
    case True
    have fo: "find_single_copy_opcode l md = (19 + md * 16 + l - 3, False)"
      using l_ge True by (simp add: find_single_copy_opcode_def Let_def)
    show ?thesis
      using ea fo l_ge
      by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  next
    case False
    have fo: "find_single_copy_opcode l md = (19 + md * 16, True)"
      using False by (simp add: find_single_copy_opcode_def Let_def)
    have vlen: "length (varint_encode l) \<le> 5"
      using varint_size_le_5_32[OF l_lt] by simp
    show ?thesis
      using ea fo vlen False
      by (simp add: emit_copy_spec_def emit_inst_spec_def Let_def)
  qed
qed

text \<open>The budget-tower flush-then-copy step: noop fused try, framed flush
  of the pending buffer, emit_copy' keystone for the COPY, budget
  preservation via the pure match-step lemma.\<close>

lemma encode_window_flush_then_copy_step_topdown:
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
proof -
  let ?Q = "\<lambda>r t. \<exists>sec' tp' pend_len' spec_st'.
              r = Result (pend_len', sec', tp') \<and>
              encode_window_loop_budget_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
              enc_tp spec_st < enc_tp spec_st' \<and>
              (((pend_len', sec', tp'), t), ((pend_len, sec, tp), s)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp)"
  let ?idx = "build_index_spec src_bytes"
  let ?mp = "match_t_C.pos_C m"
  let ?ml = "match_t_C.len_C m"
  \<comment> \<open>--- components of the budget invariant ---\<close>
  have src_heap: "heap_bytes s src (unat src_len) = src_bytes"
    and tgt_heap: "heap_bytes s tgt (unat tgt_len) = tgt_bytes"
    and src_len_eq: "length src_bytes = unat src_len"
    and tgt_len_eq: "length tgt_bytes = unat tgt_len"
    and pending_heap:
      "heap_bytes_word s pending 0 pend_len = enc_pending spec_st"
    and pending_len: "length (enc_pending spec_st) = unat pend_len"
    and tp_eq: "enc_tp spec_st = unat tp"
    and flushed_inv:
      "enc_flushed spec_st + length (enc_pending spec_st) = enc_tp spec_st"
    and sections_rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and pend_cap_le: "unat pend_len \<le> unat pending_cap"
    and addr_pos_le: "unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"
    and budget0:
      "encode_window_section_budget src_bytes tgt_bytes
        data_cap inst_cap addr_cap spec_st"
    and abs: "enc_cache_abs s (enc_cache spec_st)"
    and cwf: "enc_cache_wf (enc_cache spec_st)"
    using rel by (simp_all add: encode_window_loop_budget_rel_def)
  have data_slack:
    "unat (sections_t_C.data_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat data_cap"
    using rel unfolding encode_window_loop_budget_rel_def by blast
  have inst_slack:
    "unat (sections_t_C.inst_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat inst_cap"
    using rel unfolding encode_window_loop_budget_rel_def by blast
  have dp_len0: "length (enc_data spec_st) = unat (sections_t_C.data_pos_C sec)"
    and ip_len0: "length (enc_inst spec_st) = unat (sections_t_C.inst_pos_C sec)"
    and ap_len0: "length (enc_addr spec_st) = unat (sections_t_C.addr_pos_C sec)"
    using enc_sections_state_rel_lengths[OF sections_rel] by simp_all
  \<comment> \<open>--- match facts ---\<close>
  have tp_nat_lt: "unat tp < unat tgt_len"
    using tp_lt by (simp add: word_less_nat_alt)
  have tp_le_w: "tp \<le> tgt_len" using tp_lt by simp
  have copy_ge: "(4 :: 32 word) \<le> ?ml"
    using match_len by (simp add: min_match_def)
  have copy_ge_nat: "4 \<le> unat ?ml"
    using copy_ge by (simp add: word_le_nat_alt)
  have len_nz: "unat ?ml \<noteq> 0" using copy_ge_nat by simp
  have match_valid0:
    "match_valid src_bytes tgt_bytes (unat tp) (unat ?mp) (unat ?ml)"
    using match_rel match tp_le_w
    unfolding encode_window_match_rel_def by blast
  let ?best = "find_best_match_spec src_bytes tgt_bytes (unat tp) ?idx"
  have m_eq0: "m =
      (let best = find_best_match_spec src_bytes tgt_bytes (unat tp) ?idx
       in match_t_C (of_nat (em_pos best)) (of_nat (em_len best)))"
    using match_rel match tp_le_w
    unfolding encode_window_match_rel_def by blast
  have m_eq: "m = match_t_C (of_nat (em_pos ?best)) (of_nat (em_len ?best))"
    using m_eq0 by (simp add: Let_def)
  have not_short: "\<not> em_len ?best < min_match"
  proof
    assume short: "em_len ?best < min_match"
    have "unat ?ml = em_len ?best"
      using m_eq short by (simp add: min_match_def unat_of_nat_eq)
    thus False using copy_ge_nat short by (simp add: min_match_def)
  qed
  have min_le: "min_match \<le> em_len ?best" using not_short by simp
  have sound:
    "em_pos ?best + em_len ?best \<le> length src_bytes \<and>
     unat tp + em_len ?best \<le> length tgt_bytes \<and>
     (\<forall>k < em_len ?best.
        src_bytes ! (em_pos ?best + k) = tgt_bytes ! (unat tp + k))"
    by (rule find_best_match_spec_sound[OF refl min_le])
  have best_len32: "em_len ?best < 2 ^ 32"
  proof -
    have "em_len ?best \<le> unat tp + em_len ?best" by simp
    also have "... \<le> length tgt_bytes" using sound by simp
    also have "... = unat tgt_len" using tgt_len_eq by simp
    also have "... < 2 ^ 32" using unat_lt2p[of tgt_len] by simp
    finally show ?thesis .
  qed
  have best_pos32: "em_pos ?best < 2 ^ 32"
  proof -
    have "em_pos ?best \<le> em_pos ?best + em_len ?best" by simp
    also have "... \<le> length src_bytes" using sound by simp
    also have "... = unat src_len" using src_len_eq by simp
    also have "... < 2 ^ 32" using unat_lt2p[of src_len] by simp
    finally show ?thesis .
  qed
  have c_len: "unat ?ml = em_len ?best"
    using m_eq best_len32 by (simp add: unat_of_nat_eq)
  have c_pos: "unat ?mp = em_pos ?best"
    using m_eq best_pos32 by (simp add: unat_of_nat_eq)
  have tp_len_room_nat: "unat tp + unat ?ml \<le> unat tgt_len"
    using match_validD(2)[OF match_valid0 len_nz] tgt_len_eq by simp
  have tp_len_no_overflow: "unat tp + unat ?ml < 2 ^ 32"
    using tp_len_room_nat unat_lt2p[of tgt_len] by simp
  have tp_len_unat: "unat (tp + ?ml) = unat tp + unat ?ml"
    by (rule unat_word_add_no_overflow[OF tp_len_no_overflow])
  have tp_len_le_nat: "unat (tp + ?ml) \<le> unat tgt_len"
    using tp_len_room_nat tp_len_unat by simp
  have measure_progress:
    "unat tgt_len - unat (tp + ?ml) < unat tgt_len - unat tp"
    using tp_len_le_nat tp_len_unat copy_ge_nat tp_nat_lt by linarith
  \<comment> \<open>--- the post-step spec state and its budget ---\<close>
  define st1 where "st1 =
    (if enc_pending spec_st = [] then spec_st
     else flush_pending_spec (length src_bytes) spec_st)"
  define spec2 where "spec2 =
    emit_copy_spec (length src_bytes) (unat ?mp) (unat ?ml) st1"
  have step_eq: "spec2 = encode_window_full_step src_bytes tgt_bytes ?idx spec_st"
    using not_short fused_none c_pos c_len tp_eq
    by (simp add: encode_window_full_step_def Let_def
        flush_then_emit_copy_spec_def st1_def spec2_def)
  have tp_spec_lt: "enc_tp spec_st < length tgt_bytes"
    using tp_eq tp_nat_lt tgt_len_eq by simp
  have not_short':
    "\<not> em_len (find_best_match_spec src_bytes tgt_bytes (enc_tp spec_st)
        ?idx) < min_match"
    using not_short tp_eq by simp
  have budget2:
    "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap spec2"
    by (rule encode_window_section_budget_match_step[
          OF budget0 tp_spec_lt not_short' step_eq])
  have caps2:
    "length (enc_data spec2) \<le> unat data_cap \<and>
     length (enc_inst spec2) \<le> unat inst_cap \<and>
     length (enc_addr spec2) \<le> unat addr_cap"
  proof -
    let ?fin = "encode_window_final_spec_state src_bytes tgt_bytes"
    have pfx: "length (enc_data spec2) \<le> length (enc_data ?fin) \<and>
               length (enc_inst spec2) \<le> length (enc_inst ?fin) \<and>
               length (enc_addr spec2) \<le> length (enc_addr ?fin)"
      using budget2
      by (simp add: encode_window_section_budget_def
          encode_window_section_prefix_budget_def)
    have fin: "length (enc_data ?fin) \<le> unat data_cap \<and>
               length (enc_inst ?fin) \<le> unat inst_cap \<and>
               length (enc_addr ?fin) \<le> unat addr_cap"
      using budget2
      by (simp add: encode_window_section_budget_def
          encoder_final_section_caps_ok_def)
    show ?thesis using pfx fin by linarith
  qed
  \<comment> \<open>--- pure facts about the flushed intermediate state ---\<close>
  have pending_lt32: "length (enc_pending spec_st) < 2 ^ 32"
    using pending_len unat_lt2p[of pend_len] by simp
  have st1_pending: "enc_pending st1 = []"
    by (simp add: st1_def flush_pending_spec_def)
  have st1_tp: "enc_tp st1 = enc_tp spec_st"
    by (simp add: st1_def flush_pending_spec_enc_tp)
  have st1_flushed: "enc_flushed st1 = enc_tp spec_st"
    using flushed_inv
    by (auto simp: st1_def flush_pending_spec_flushed)
  have st1_cache: "enc_cache st1 = enc_cache spec_st"
    by (simp add: st1_def flush_pending_spec_cache)
  have st1_data_le:
    "length (enc_data st1) \<le> length (enc_data spec_st) + unat pend_len"
    using flush_pending_spec_growth_bounds(1)[OF pending_lt32] pending_len
    by (auto simp: st1_def)
  have st1_inst_le:
    "length (enc_inst st1) \<le> length (enc_inst spec_st) + unat pend_len"
    using flush_pending_spec_growth_bounds(2)[OF pending_lt32] pending_len
    by (auto simp: st1_def)
  have mono1:
    "length (enc_data st1) \<le> length (enc_data spec2) \<and>
     length (enc_inst st1) \<le> length (enc_inst spec2) \<and>
     length (enc_addr st1) \<le> length (enc_addr spec2)"
    using emit_copy_spec_sections_mono[of st1 "length src_bytes"]
    by (simp add: spec2_def)
  have data_room1: "length (enc_data st1) \<le> unat data_cap"
    using mono1 caps2 by linarith
  have inst_room_k:
    "length (enc_inst (emit_copy_spec (length src_bytes) (unat ?mp)
       (unat ?ml) st1)) \<le> unat inst_cap"
    using caps2 by (simp add: spec2_def)
  have addr_room_k:
    "length (enc_addr (emit_copy_spec (length src_bytes) (unat ?mp)
       (unat ?ml) st1)) \<le> unat addr_cap"
    using caps2 by (simp add: spec2_def)
  \<comment> \<open>--- rooms for the framed flush ---\<close>
  have flush_data_room64:
    "length (enc_data (flush_pending_spec (length src_bytes) spec_st)) + 64
      \<le> unat data_cap"
    using flush_pending_spec_growth_bounds(1)[OF pending_lt32,
        of "length src_bytes"]
      pending_len dp_len0 data_slack
    by linarith
  have flush_inst_room64:
    "length (enc_inst (flush_pending_spec (length src_bytes) spec_st)) + 64
      \<le> unat inst_cap"
    using flush_pending_spec_growth_bounds(2)[OF pending_lt32,
        of "length src_bytes"]
      pending_len ip_len0 inst_slack
    by linarith
  have flush_addr_room:
    "length (enc_addr (flush_pending_spec (length src_bytes) spec_st))
      \<le> unat addr_cap"
    using flush_pending_spec_growth_bounds(3)[OF pending_lt32,
        of "length src_bytes"]
      ap_len0 addr_pos_le
    by simp
  \<comment> \<open>--- best mode facts for the noop ---\<close>
  obtain bm where bm: "best_mode' ?mp (src_len + tp) s = Some bm"
    by (rule best_mode'_some[OF abs cwf])
  have mode_wf:
    "enc_mode_arg_wf (enc_cache spec_st) ?mp (src_len + tp) bm"
    by (rule best_mode'_encode_address_correct[OF abs cwf bm])
  have mode_le8: "mode_t_C.mode_C bm \<le> (8 :: 32 word)"
    by (rule enc_mode_arg_wf_mode_word_le8[OF mode_wf])
  have src_tp_no: "unat src_len + unat tp < 2 ^ 32"
    using src_len_eq tgt_len_eq src_tgt_bound tp_nat_lt by linarith
  have here_eq: "unat (src_len + tp) = length src_bytes + enc_tp spec_st"
    using src_len_eq tp_eq src_tp_no
    by (simp add: unat_word_ariths)
  have addr_exact:
    "encode_address (enc_cache spec_st) (unat ?mp)
       (length src_bytes + enc_tp spec_st) =
     (unat (mode_t_C.mode_C bm),
      enc_best_bytes (mode_t_C.mode_C bm) (mode_t_C.arg_C bm),
      cache_update (enc_cache spec_st) (unat ?mp))"
    using best_mode'_encode_address_exact[OF abs cwf bm] here_eq by simp
  \<comment> \<open>--- spec facts about the post-copy state ---\<close>
  have tp2_eq: "enc_tp spec2 = unat (tp + ?ml)"
    using emit_copy_spec_components(2)[of "length src_bytes"] st1_tp tp_eq
      tp_len_unat
    by (simp add: spec2_def)
  have flushed2_eq: "enc_flushed spec2 = enc_tp spec2"
    using emit_copy_spec_components(2,3)[of "length src_bytes"]
      st1_flushed st1_tp
    by (simp add: spec2_def)
  have pending2: "enc_pending spec2 = []"
    using emit_copy_spec_components(1)[of "length src_bytes"] st1_pending
    by (simp add: spec2_def)
  have data2_len_le:
    "length (enc_data spec2) \<le>
     unat (sections_t_C.data_pos_C sec) + unat pend_len"
    using emit_copy_spec_components(4)[of "length src_bytes"]
      st1_data_le dp_len0
    by (simp add: spec2_def)
  have ml_lt32: "unat ?ml < 2 ^ 32"
    using unat_lt2p[of ?ml] by simp
  have inst2_len_le:
    "length (enc_inst spec2) \<le>
     unat (sections_t_C.inst_pos_C sec) + unat pend_len + unat ?ml"
    using emit_copy_spec_inst_growth_le_len[OF copy_ge_nat ml_lt32,
        of "length src_bytes" "unat ?mp" st1]
      st1_inst_le ip_len0
    by (simp add: spec2_def)
  have tp_progress2: "enc_tp spec_st < enc_tp spec2"
    using tp2_eq tp_eq tp_len_unat copy_ge_nat by simp
  \<comment> \<open>--- budget invariant after the copy ---\<close>
  have rel_after:
    "\<And>u sec2. \<lbrakk>
        sections_t_C.err_C sec2 = ENC_OK;
        enc_sections_state_rel u data inst addr sec2 spec2;
        enc_cache_abs u (enc_cache spec2);
        enc_cache_wf (enc_cache spec2);
        heap_bytes u src (unat src_len) = src_bytes;
        heap_bytes u tgt (unat tgt_len) = tgt_bytes \<rbrakk> \<Longrightarrow>
      encode_window_loop_budget_rel u src src_len tgt tgt_len
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        sec2 (tp + ?ml) 0 src_bytes tgt_bytes spec2"
  proof -
    fix u sec2
    assume ok2: "sections_t_C.err_C sec2 = ENC_OK"
      and srel2: "enc_sections_state_rel u data inst addr sec2 spec2"
      and cabs2: "enc_cache_abs u (enc_cache spec2)"
      and cwf2: "enc_cache_wf (enc_cache spec2)"
      and srcu: "heap_bytes u src (unat src_len) = src_bytes"
      and tgtu: "heap_bytes u tgt (unat tgt_len) = tgt_bytes"
    have dp2_len: "length (enc_data spec2) =
        unat (sections_t_C.data_pos_C sec2)"
      and ip2_len: "length (enc_inst spec2) =
        unat (sections_t_C.inst_pos_C sec2)"
      and ap2_len: "length (enc_addr spec2) =
        unat (sections_t_C.addr_pos_C sec2)"
      using enc_sections_state_rel_lengths[OF srel2] by simp_all
    have pending_u: "heap_bytes_word u pending 0 0 = enc_pending spec2"
      using pending2 by (simp add: heap_bytes_word_def)
    have data_slack2:
      "unat (sections_t_C.data_pos_C sec2) + unat (0 :: 32 word) +
         (unat tgt_len - unat (tp + ?ml)) + 64 \<le> unat data_cap"
    proof -
      have z: "unat (0 :: 32 word) = 0" by simp
      show ?thesis
        using dp2_len data2_len_le data_slack tp_len_unat tp_len_le_nat z
        by linarith
    qed
    have inst_slack2:
      "unat (sections_t_C.inst_pos_C sec2) + unat (0 :: 32 word) +
         (unat tgt_len - unat (tp + ?ml)) + 64 \<le> unat inst_cap"
    proof -
      have z: "unat (0 :: 32 word) = 0" by simp
      show ?thesis
        using ip2_len inst2_len_le inst_slack tp_len_unat tp_len_le_nat z
        by linarith
    qed
    show "encode_window_loop_budget_rel u src src_len tgt tgt_len
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        sec2 (tp + ?ml) 0 src_bytes tgt_bytes spec2"
      using srcu tgtu src_len_eq tgt_len_eq pending_u pending2
        tp2_eq flushed2_eq srel2 ok2 tp_len_le_nat
        dp2_len ip2_len ap2_len caps2 data_slack2 inst_slack2
        budget2 cabs2 cwf2
      by (auto simp: encode_window_loop_budget_rel_def)
  qed
  \<comment> \<open>--- noop run of the fused try ---\<close>
  have noop_run:
    "try_emit_add_copy' sec data data_cap inst inst_cap addr addr_cap
        pending pend_len ?mp (src_len + tp) ?ml \<bullet> s
      \<lbrace> \<lambda>r t.
          (\<exists>f. r = Result f \<and>
               fused_t_C.s_C f = sec \<and>
               fused_t_C.fused_C f = 0) \<and>
          t = s \<rbrace>"
    by (rule try_emit_add_copy'_spec_none_noop[
          OF sections_rel pending_len copy_ge fused_none bm mode_le8
             addr_exact])
  \<comment> \<open>--- flush stage of the C else-branch ---\<close>
  have flush_stage:
    "condition (\<lambda>s. 0 < pend_len)
       (do {
          sec_run \<leftarrow> liftE
            (flush_pending' sec data data_cap inst inst_cap
              pending pend_len);
          unless (sections_t_C.err_C sec_run = 0) (throw sec_run);
          return (0, sec_run)
        })
       (return (pend_len, sec)) \<bullet> s
     \<lbrace> \<lambda>r t1. \<exists>sec1.
          r = Result ((0 :: 32 word), sec1) \<and>
          enc_sections_state_rel t1 data inst addr sec1 st1 \<and>
          sections_t_C.err_C sec1 = ENC_OK \<and>
          heap_bytes t1 src (unat src_len) = src_bytes \<and>
          heap_bytes t1 tgt (unat tgt_len) = tgt_bytes \<and>
          enc_cache_abs t1 (enc_cache spec_st) \<and>
          heap_typing t1 = heap_typing s \<rbrace>"
  proof (cases "0 < pend_len")
    case pend_pos: True
    have pend_nz_nat: "0 < unat pend_len"
      using pend_pos by (simp add: word_less_nat_alt)
    have pending_ne: "enc_pending spec_st \<noteq> []"
      using pending_len pend_nz_nat by auto
    have st1_flush: "st1 = flush_pending_spec (length src_bytes) spec_st"
      using pending_ne by (simp add: st1_def)
    have FH:
      "flush_pending' sec data data_cap inst inst_cap pending pend_len \<bullet> s
       \<lbrace> \<lambda>r t1. \<exists>sec'.
            r = Result sec' \<and>
            enc_sections_state_rel t1 data inst addr sec'
              (flush_pending_spec (length src_bytes) spec_st) \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            heap_bytes_word t1 src 0 src_len =
              heap_bytes_word s src 0 src_len \<and>
            heap_bytes_word t1 tgt 0 tgt_len =
              heap_bytes_word s tgt 0 tgt_len \<and>
            enc_cache_abs t1 (enc_cache spec_st) \<and>
            heap_typing t1 = heap_typing s \<rbrace>"
      by (rule flush_pending'_loop_from_final_fits_framed[
            OF buffers sections_rel abs cwf sec_ok pending_heap[symmetric]
               pend_cap_le flush_data_room64 flush_inst_room64
               flush_addr_room])
    have FH_lifted:
      "liftE (flush_pending' sec data data_cap inst inst_cap
          pending pend_len) \<bullet> s
       \<lbrace> \<lambda>r t1. \<exists>sec'.
            r = Result sec' \<and>
            enc_sections_state_rel t1 data inst addr sec' st1 \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            heap_bytes t1 src (unat src_len) = src_bytes \<and>
            heap_bytes t1 tgt (unat tgt_len) = tgt_bytes \<and>
            enc_cache_abs t1 (enc_cache spec_st) \<and>
            heap_typing t1 = heap_typing s \<rbrace>"
      apply (rule runs_to_liftE)
      apply (rule runs_to_weaken[OF FH])
      using st1_flush src_heap tgt_heap
      by (auto simp: heap_bytes_word_zero)
    show ?thesis
      using pend_pos
      apply (simp add: runs_to_condition_iff)
      apply (rule runs_to_bind)
      apply (rule runs_to_weaken[OF FH_lifted])
      by (auto simp: runs_to_bind_iff)
  next
    case False
    have pend0: "pend_len = 0"
      using False by (simp add: word_neq_0_conv not_less)
    have pending_nil: "enc_pending spec_st = []"
      using pending_len pend0 by simp
    have st1_id: "st1 = spec_st"
      using pending_nil by (simp add: st1_def)
    show ?thesis
      using False pend0 st1_id sections_rel sec_ok src_heap tgt_heap abs
      by (auto simp: runs_to_condition_iff)
  qed
  \<comment> \<open>--- the else-branch continuation after the flush stage ---\<close>
  let ?cont2 =
    "\<lambda>(pend_len_run :: 32 word, sec_run). do {
        sec_run2 \<leftarrow> liftE
          (emit_copy' sec_run inst inst_cap addr addr_cap
            ?mp (src_len + tp) ?ml);
        unless (sections_t_C.err_C sec_run2 = 0) (throw sec_run2);
        return (pend_len_run, sec_run2, tp + ?ml)
      }"
  have flush_for_bind:
    "condition (\<lambda>s. 0 < pend_len)
       (do {
          sec_run \<leftarrow> liftE
            (flush_pending' sec data data_cap inst inst_cap
              pending pend_len);
          unless (sections_t_C.err_C sec_run = 0) (throw sec_run);
          return (0, sec_run)
        })
       (return (pend_len, sec)) \<bullet> s
     \<lbrace> \<lambda>r t1.
          (\<forall>v. r = Result v \<longrightarrow> ?cont2 v \<bullet> t1 \<lbrace> ?Q \<rbrace>) \<and>
          (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> ?Q (Exception e) t1) \<rbrace>"
  proof (rule runs_to_weaken[OF flush_stage])
    fix r t1
    assume "\<exists>sec1.
          r = Result ((0 :: 32 word), sec1) \<and>
          enc_sections_state_rel t1 data inst addr sec1 st1 \<and>
          sections_t_C.err_C sec1 = ENC_OK \<and>
          heap_bytes t1 src (unat src_len) = src_bytes \<and>
          heap_bytes t1 tgt (unat tgt_len) = tgt_bytes \<and>
          enc_cache_abs t1 (enc_cache spec_st) \<and>
          heap_typing t1 = heap_typing s"
    then obtain sec1 where
        r_def: "r = Result ((0 :: 32 word), sec1)"
      and srel1: "enc_sections_state_rel t1 data inst addr sec1 st1"
      and sec1_ok: "sections_t_C.err_C sec1 = ENC_OK"
      and src_t1: "heap_bytes t1 src (unat src_len) = src_bytes"
      and tgt_t1: "heap_bytes t1 tgt (unat tgt_len) = tgt_bytes"
      and abs_t1: "enc_cache_abs t1 (enc_cache spec_st)"
      and typing_t1: "heap_typing t1 = heap_typing s"
      by blast
    have abs_t1': "enc_cache_abs t1 (enc_cache st1)"
      using abs_t1 st1_cache by simp
    have cwf1: "enc_cache_wf (enc_cache st1)"
      using cwf st1_cache by simp
    have buffers_t1:
      "encode_window_loop_buffers_ok t1 src src_len tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
      by (rule encode_window_loop_buffers_ok_heap_typing[OF buffers typing_t1])
    obtain bm2 where bm2: "best_mode' ?mp (src_len + tp) t1 = Some bm2"
      by (rule best_mode'_some[OF abs_t1' cwf1])
    have here_eq1:
      "unat (src_len + tp) = length src_bytes + enc_flushed st1"
      using here_eq st1_flushed by simp
    have addr_exact2:
      "encode_address (enc_cache st1) (unat ?mp)
         (length src_bytes + enc_flushed st1) =
       (unat (mode_t_C.mode_C bm2),
        enc_best_bytes (mode_t_C.mode_C bm2) (mode_t_C.arg_C bm2),
        cache_update (enc_cache st1) (unat ?mp))"
      using best_mode'_encode_address_exact[OF abs_t1' cwf1 bm2] here_eq1
      by simp
    have cache2_eq:
      "enc_cache spec2 = cache_update (enc_cache st1) (unat ?mp)"
      using emit_copy_spec_cache_of_encode_address[OF addr_exact2]
      by (simp add: spec2_def)
    have dpos_le1:
      "unat (sections_t_C.data_pos_C sec1) \<le> unat data_cap"
      using enc_sections_state_rel_lengths(1)[OF srel1] data_room1 by simp
    have EK:
      "emit_copy' sec1 inst inst_cap addr addr_cap
         ?mp (src_len + tp) ?ml \<bullet> t1
       \<lbrace> \<lambda>r u. \<exists>sec2.
            r = Result sec2 \<and>
            sections_t_C.err_C sec2 = ENC_OK \<and>
            sections_t_C.data_pos_C sec2 = sections_t_C.data_pos_C sec1 \<and>
            unat (sections_t_C.inst_pos_C sec2) \<le> unat inst_cap \<and>
            unat (sections_t_C.addr_pos_C sec2) \<le> unat addr_cap \<and>
            enc_sections_state_rel u data inst addr sec2
              (emit_copy_spec (length src_bytes) (unat ?mp)
                (unat ?ml) st1) \<and>
            enc_cache_abs u
              (cache_update (enc_cache st1) (unat ?mp)) \<and>
            enc_cache_wf
              (cache_update (enc_cache st1) (unat ?mp)) \<and>
            heap_bytes u src (unat src_len) =
              heap_bytes t1 src (unat src_len) \<and>
            heap_bytes u tgt (unat tgt_len) =
              heap_bytes t1 tgt (unat tgt_len) \<and>
            heap_typing u = heap_typing t1 \<rbrace>"
      by (rule emit_copy'_state_rel_cache_frame_from_loop[
            OF buffers_t1 srel1 abs_t1' cwf1 bm2 addr_exact2 sec1_ok
               dpos_le1 inst_room_k addr_room_k])
    have EK_lifted:
      "liftE (emit_copy' sec1 inst inst_cap addr addr_cap
          ?mp (src_len + tp) ?ml) \<bullet> t1
       \<lbrace> \<lambda>r u. \<exists>sec2. r = Result sec2 \<and>
            sections_t_C.err_C sec2 = 0 \<and>
            ?Q (Result (0, sec2, tp + ?ml)) u \<rbrace>"
      apply (rule runs_to_liftE)
      apply (rule runs_to_weaken[OF EK])
      apply clarsimp
      subgoal for secx u
        apply (rule exI[where x = spec2])
        using rel_after[of secx u] cache2_eq spec2_def src_t1 tgt_t1
          tp_progress2 measure_progress
        by auto
      done
    show "(\<forall>v. r = Result v \<longrightarrow> ?cont2 v \<bullet> t1 \<lbrace> ?Q \<rbrace>) \<and>
          (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> ?Q (Exception e) t1)"
    proof (intro conjI allI impI)
      fix v
      assume rv: "r = Result v"
      have v_eq: "v = ((0 :: 32 word), sec1)"
        using r_def rv by simp
      have body:
        "?cont2 ((0 :: 32 word), sec1) \<bullet> t1 \<lbrace> ?Q \<rbrace>"
        apply simp
        apply (rule runs_to_bind)
        apply (rule runs_to_weaken[OF EK_lifted])
        by (auto simp: runs_to_bind_iff)
      show "?cont2 v \<bullet> t1 \<lbrace> ?Q \<rbrace>"
        using v_eq body by simp
    next
      fix e
      assume "r = Exception e" and "e \<noteq> default"
      then show "?Q (Exception e) t1"
        using r_def by simp
    qed
  qed
  \<comment> \<open>--- the continuation of the C match branch after the fused try ---\<close>
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
                      (match_t_C.pos_C m + fused_t_C.fused_C f)
                      (src_len + (tp + fused_t_C.fused_C f))
                      (match_t_C.len_C m - fused_t_C.fused_C f));
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
  have none_cont:
    "\<And>f. \<lbrakk> fused_t_C.s_C f = sec; fused_t_C.fused_C f = 0 \<rbrakk> \<Longrightarrow>
        ?cont f \<bullet> s \<lbrace> ?Q \<rbrace>"
  proof -
    fix f
    assume scf: "fused_t_C.s_C f = sec"
      and fz0: "fused_t_C.fused_C f = 0"
    have B_run:
      "(do {
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
          sec_run2 \<leftarrow> liftE
            (emit_copy' sec_run inst inst_cap addr addr_cap
              ?mp (src_len + tp) ?ml);
          unless (sections_t_C.err_C sec_run2 = 0)
            (throw sec_run2);
          return (pend_len_run, sec_run2, tp + ?ml)
        }) \<bullet> s \<lbrace> ?Q \<rbrace>"
      by (rule runs_to_bind[OF flush_for_bind])
    show "?cont f \<bullet> s \<lbrace> ?Q \<rbrace>"
      using B_run by (simp add: scf fz0 sec_ok)
  qed
  \<comment> \<open>--- assemble the branch ---\<close>
  have noop_lifted:
    "liftE (try_emit_add_copy' sec data data_cap inst inst_cap
        addr addr_cap pending pend_len ?mp (src_len + tp) ?ml) \<bullet> s
     \<lbrace> \<lambda>r t. \<exists>f.
          r = Result f \<and>
          fused_t_C.s_C f = sec \<and>
          fused_t_C.fused_C f = 0 \<and>
          t = s \<rbrace>"
    apply (rule runs_to_liftE)
    apply (rule runs_to_weaken[OF noop_run])
    by auto
  have noop_for_bind:
    "liftE (try_emit_add_copy' sec data data_cap inst inst_cap
        addr addr_cap pending pend_len ?mp (src_len + tp) ?ml) \<bullet> s
     \<lbrace> \<lambda>r t.
          (\<forall>v. r = Result v \<longrightarrow> ?cont v \<bullet> t \<lbrace> ?Q \<rbrace>) \<and>
          (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> ?Q (Exception e) t) \<rbrace>"
  proof (rule runs_to_weaken[OF noop_lifted])
    fix r t
    assume "\<exists>f. r = Result f \<and> fused_t_C.s_C f = sec \<and>
        fused_t_C.fused_C f = 0 \<and> t = s"
    then obtain f where r_def: "r = Result f"
      and scf: "fused_t_C.s_C f = sec"
      and fz0: "fused_t_C.fused_C f = 0"
      and t_eq: "t = s"
      by blast
    have cont_f: "?cont f \<bullet> t \<lbrace> ?Q \<rbrace>"
      using none_cont[OF scf fz0] t_eq by simp
    show "(\<forall>v. r = Result v \<longrightarrow> ?cont v \<bullet> t \<lbrace> ?Q \<rbrace>) \<and>
          (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> ?Q (Exception e) t)"
      using r_def cont_f by auto
  qed
  have branch_unfold:
    "encode_window_c_match_branch src_len
       data data_cap inst inst_cap addr addr_cap
       pending pend_len sec tp m =
     bind (liftE
       (try_emit_add_copy' sec data data_cap inst inst_cap
         addr addr_cap pending pend_len ?mp (src_len + tp) ?ml)) ?cont"
    by (simp add: encode_window_c_match_branch_def)
  show ?thesis
    apply (subst branch_unfold)
    apply (rule runs_to_bind[OF noop_for_bind])
    done
qed

lemma encode_window_match_step_topdown:
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
    by (rule encode_window_pending_byte_step_topdown[
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

text \<open>Partial-correctness frame: the encode-window loop body only writes the
  byte heap and the address-cache globals, so the 32-bit word heap (holding
  the source index arrays) and the heap typing are untouched.  Proved
  bottom-up through the emit layer; combined with the total budget step via
  runs_to_of_runs_to_partial_runs_to' to thread encoder_index_post through
  the loop.\<close>

lemma write_byte'_w32_typing_frame:
  "write_byte' buf cap pos b \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding write_byte'_def
  by runs_to_vcg

lemma write_varint'_w32_typing_frame:
  "write_varint' buf cap pos v \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding write_varint'_def
  apply runs_to_vcg
  apply (rule runs_to_partial_whileLoop_res[
     where I = "\<lambda>_ t. heap_w32 t = heap_w32 s \<and>
                      heap_typing t = heap_typing s"])
    apply simp
   apply auto[1]
  apply runs_to_vcg
  done

lemma write_bytes'_w32_typing_frame:
  "write_bytes' buf cap pos src src_off len \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  apply (rule runs_to_partial_whileLoop_res[
     where I = "\<lambda>_ t. heap_w32 t = heap_w32 s \<and>
                      heap_typing t = heap_typing s"])
    apply simp
   apply auto[1]
  apply runs_to_vcg
  done

lemma emit_address'_w32_typing_frame:
  "emit_address' addr_buf addr_cap addr_pos m \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_address'_def
  supply write_byte'_w32_typing_frame[runs_to_vcg]
  supply write_varint'_w32_typing_frame[runs_to_vcg]
  by runs_to_vcg

lemma cache_update'_w32_typing_frame:
  "cache_update' a \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding cache_update'_def
  by runs_to_vcg

lemma emit_add'_w32_typing_frame:
  "emit_add' sec data data_cap inst inst_cap pending off sz \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_add'_def
  supply write_byte'_w32_typing_frame[runs_to_vcg]
  supply write_varint'_w32_typing_frame[runs_to_vcg]
  supply write_bytes'_w32_typing_frame[runs_to_vcg]
  by runs_to_vcg auto

lemma emit_run'_w32_typing_frame:
  "emit_run' sec data data_cap inst inst_cap fill sz \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_run'_def
  supply write_byte'_w32_typing_frame[runs_to_vcg]
  supply write_varint'_w32_typing_frame[runs_to_vcg]
  by runs_to_vcg auto

lemma emit_copy'_w32_typing_frame:
  "emit_copy' sec inst inst_cap addr_buf addr_cap copy_addr here copy_len
     \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding emit_copy'_def
  supply write_byte'_w32_typing_frame[runs_to_vcg]
  supply write_varint'_w32_typing_frame[runs_to_vcg]
  supply emit_address'_w32_typing_frame[runs_to_vcg]
  supply cache_update'_w32_typing_frame[runs_to_vcg]
  by runs_to_vcg auto

lemma add_copy_opcode'_w32_typing_frame:
  "add_copy_opcode' add_sz copy_sz mode \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding add_copy_opcode'_def
  by runs_to_vcg

lemma try_emit_add_copy'_w32_typing_frame:
  "try_emit_add_copy' sec data data_cap inst inst_cap addr_buf addr_cap
      pending pend_len copy_addr here copy_len \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding try_emit_add_copy'_def
  supply add_copy_opcode'_w32_typing_frame[runs_to_vcg]
  supply write_byte'_w32_typing_frame[runs_to_vcg]
  supply write_bytes'_w32_typing_frame[runs_to_vcg]
  supply emit_address'_w32_typing_frame[runs_to_vcg]
  supply cache_update'_w32_typing_frame[runs_to_vcg]
  by runs_to_vcg auto

lemma flush_pending_scan_loop_w32_typing_frame:
  "(whileLoop (\<lambda>(j, ret) s. ret \<noteq> (0 :: 32 word))
      (\<lambda>(j, ret). do {
         x \<leftarrow> guard (\<lambda>s. j + 1 < len \<longrightarrow>
                IS_VALID(8 word) s (pending +\<^sub>p uint (j + 1)));
         ret \<leftarrow> gets (\<lambda>s. j + 1 < len \<and>
                heap_w8 s (pending +\<^sub>p uint (j + 1)) = b);
         return (j + 1, if ret then (1 :: 32 word) else 0)
       }) jr0 :: (32 word \<times> 32 word, lifted_globals) res_monad) \<bullet> s
   ?\<lbrace> \<lambda>r t. heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_partial_whileLoop_res[
    where I = "\<lambda>_ t. heap_w32 t = heap_w32 s \<and>
                     heap_typing t = heap_typing s"])
    apply simp
   apply simp
  subgoal for a t
    apply (cases a)
    apply clarsimp
    apply runs_to_vcg
    done
  done

lemma flush_pending'_w32_typing_frame:
  "flush_pending' sec data data_cap inst inst_cap pending pend_len
     \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding flush_pending'_def
  supply emit_add'_w32_typing_frame[runs_to_vcg]
  supply emit_run'_w32_typing_frame[runs_to_vcg]
  apply runs_to_vcg
  apply (rule runs_to_partial_whileLoop_exn[
     where I = "\<lambda>r t. heap_w32 t = heap_w32 s \<and>
                      heap_typing t = heap_typing s"])
     apply simp
    apply (runs_to_vcg, (auto)?)
   apply (runs_to_vcg, (auto)?)
  apply (runs_to_vcg, (auto)?)
  subgoal for a aa b sa
    apply (rule runs_to_partial_weaken)
     apply (rule runs_to_partial_whileLoop_res[
       where P = "\<lambda>r (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"
         and I = "\<lambda>_ (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"])
       apply simp
      apply simp
     subgoal for x u
       apply (cases x)
       apply clarsimp
       apply runs_to_vcg
       done
    apply clarsimp
    apply (runs_to_vcg, (auto)?)
    done
  subgoal for a aa b sa
    apply (rule runs_to_partial_weaken)
     apply (rule runs_to_partial_whileLoop_res[
       where P = "\<lambda>r (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"
         and I = "\<lambda>_ (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"])
       apply simp
      apply simp
     subgoal for x u
       apply (cases x)
       apply clarsimp
       apply runs_to_vcg
       done
    apply clarsimp
    apply (runs_to_vcg, (auto)?)
    done
  subgoal for a aa b sa
    apply (rule runs_to_partial_weaken)
     apply (rule runs_to_partial_whileLoop_res[
       where P = "\<lambda>r (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"
         and I = "\<lambda>_ (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"])
       apply simp
      apply simp
     subgoal for x u
       apply (cases x)
       apply clarsimp
       apply runs_to_vcg
       done
    apply clarsimp
    apply (runs_to_vcg, (auto)?)
    done
  subgoal for a aa b sa
    apply (rule runs_to_partial_weaken)
     apply (rule runs_to_partial_whileLoop_res[
       where P = "\<lambda>r (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"
         and I = "\<lambda>_ (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"])
       apply simp
      apply simp
     subgoal for x u
       apply (cases x)
       apply clarsimp
       apply runs_to_vcg
       done
    apply clarsimp
    apply (runs_to_vcg, (auto)?)
    done
  subgoal for a aa b sa
    apply (rule runs_to_partial_weaken)
     apply (rule runs_to_partial_whileLoop_res[
       where P = "\<lambda>r (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"
         and I = "\<lambda>_ (u :: lifted_globals).
                    heap_w32 u = heap_w32 s \<and>
                    heap_typing u = heap_typing s"])
       apply simp
      apply simp
     subgoal for x u
       apply (cases x)
       apply clarsimp
       apply runs_to_vcg
       done
    apply clarsimp
    apply (runs_to_vcg, (auto)?)
    done
  done

lemma encode_window_c_loop_body_w32_typing_frame:
  "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
      data data_cap inst inst_cap addr addr_cap pending pending_cap
      (pl0, sc0, tp0) \<bullet> s ?\<lbrace> \<lambda>r t.
      heap_w32 t = heap_w32 s \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding encode_window_c_loop_body_def case_prod_conv
  supply try_emit_add_copy'_w32_typing_frame[runs_to_vcg]
  supply emit_copy'_w32_typing_frame[runs_to_vcg]
  supply flush_pending'_w32_typing_frame[runs_to_vcg]
  apply runs_to_vcg
  apply auto
  done

text \<open>encoder_index_post transports along the w32/typing frame, given the
  src/tgt byte contents are re-established (they come from the budget
  invariant).\<close>

lemma encoder_index_post_w32_typing_transport:
  assumes index:
      "encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
        src_bytes tgt_bytes"
    and w32: "heap_w32 u = heap_w32 t"
    and typing: "heap_typing u = heap_typing t"
    and src_u: "heap_bytes u src (unat src_len) = src_bytes"
    and tgt_u: "heap_bytes u tgt (unat tgt_len) = tgt_bytes"
  shows "encoder_index_post s0 u src src_len tgt tgt_len head_arr next_arr
        src_bytes tgt_bytes"
  using index w32 typing src_u tgt_u
  by (simp add: encoder_index_post_def source_index_heap_rel_def
      source_index_heap_nexts_wf_def source_index_heap_chains_closed_def
      heap_w32_list_def)

text \<open>Totality of the match finder: under the index invariants and buffer
  validity, common_prefix' and find_best_match' never return None.  This is
  what lets the encode-window loop's gets_the succeed at every iteration.\<close>

lemma common_prefix'_isSome:
  fixes a_buf b_buf :: "8 word ptr"
    and a_pos a_end b_pos b_end :: "32 word"
  assumes a_valid: "buf_valid s a_buf (unat a_end)"
      and b_valid: "buf_valid s b_buf (unat b_end)"
      and a_le: "a_pos \<le> a_end"
      and b_le: "b_pos \<le> b_end"
  shows "\<exists>l. common_prefix' a_buf a_pos a_end b_buf b_pos b_end s = Some l"
proof -
  define limit where "limit =
    (if a_end - a_pos < b_end - b_pos then a_end - a_pos else b_end - b_pos)"
  have limit_le_a: "limit \<le> a_end - a_pos"
    by (auto simp: limit_def linorder_not_less)
  have limit_le_b: "limit \<le> b_end - b_pos"
    by (auto simp: limit_def linorder_not_less)
  have VA: "\<And>k :: 32 word. k < limit \<Longrightarrow>
      ptr_valid (heap_typing s) (a_buf +\<^sub>p uint (a_pos + k))"
  proof -
    fix k :: "32 word"
    assume k_lt: "k < limit"
    have k_lt_a: "k < a_end - a_pos"
      using k_lt limit_le_a by simp
    have k_nat: "unat k < unat a_end - unat a_pos"
      using k_lt_a a_le
      by (simp add: word_less_nat_alt unat_sub)
    have no: "unat a_pos + unat k < unat a_end"
      using k_nat by linarith
    have no32: "unat a_pos + unat k < 2 ^ 32"
      using no unat_lt2p[of a_end] by simp
    have unat_eq: "unat (a_pos + k) = unat a_pos + unat k"
      by (rule unat_word_add_no_overflow[OF no32])
    have lt: "unat (a_pos + k) < unat a_end"
      using unat_eq no by simp
    show "ptr_valid (heap_typing s) (a_buf +\<^sub>p uint (a_pos + k))"
      by (rule buf_valid_uintD[OF a_valid lt])
  qed
  have VB: "\<And>k :: 32 word. k < limit \<Longrightarrow>
      ptr_valid (heap_typing s) (b_buf +\<^sub>p uint (b_pos + k))"
  proof -
    fix k :: "32 word"
    assume k_lt: "k < limit"
    have k_lt_b: "k < b_end - b_pos"
      using k_lt limit_le_b by simp
    have k_nat: "unat k < unat b_end - unat b_pos"
      using k_lt_b b_le
      by (simp add: word_less_nat_alt unat_sub)
    have no: "unat b_pos + unat k < unat b_end"
      using k_nat by linarith
    have no32: "unat b_pos + unat k < 2 ^ 32"
      using no unat_lt2p[of b_end] by simp
    have unat_eq: "unat (b_pos + k) = unat b_pos + unat k"
      by (rule unat_word_add_no_overflow[OF no32])
    have lt: "unat (b_pos + k) < unat b_end"
      using unat_eq no by simp
    show "ptr_valid (heap_typing s) (b_buf +\<^sub>p uint (b_pos + k))"
      by (rule buf_valid_uintD[OF b_valid lt])
  qed
  let ?C = "\<lambda>(n :: 32 word, ret :: int) s. ret \<noteq> 0"
  let ?B = "\<lambda>(n :: 32 word, ret :: int).
    do {
      ret <-
        ocondition
          (\<lambda>s. n + 1 < limit)
          (do {
             oguard
              (\<lambda>st.
                  IS_VALID(8 word) st
                    (b_buf +\<^sub>p uint (b_pos + (n + 1))) \<and>
                  IS_VALID(8 word) st
                    (a_buf +\<^sub>p uint (a_pos + (n + 1))));
             ogets
              (\<lambda>s. if heap_w8 s (a_buf +\<^sub>p uint (a_pos + (n + 1))) =
                      heap_w8 s (b_buf +\<^sub>p uint (b_pos + (n + 1)))
                   then 1 else 0)
           })
          (oreturn 0);
      oreturn (n + 1, ret)
    }"
  let ?Init =
    "ocondition
      (\<lambda>s. 0 < limit)
      (do {
         oguard
          (\<lambda>st.
              IS_VALID(8 word) st (b_buf +\<^sub>p uint b_pos) \<and>
              IS_VALID(8 word) st (a_buf +\<^sub>p uint a_pos));
         ogets
          (\<lambda>s. if heap_w8 s (a_buf +\<^sub>p uint a_pos) =
                  heap_w8 s (b_buf +\<^sub>p uint b_pos)
               then 1 else 0)
       })
      (oreturn 0)"
  let ?I = "\<lambda>(n :: 32 word, ret :: int) s. ret \<noteq> 0 \<longrightarrow> n < limit"
  have unfolded:
    "common_prefix' a_buf a_pos a_end b_buf b_pos b_end s =
      (do {
         ret <- ?Init;
         (n, ret) <- owhile ?C ?B (0, ret);
         oreturn n
       }) s"
    unfolding common_prefix'_def limit_def[symmetric]
    by (simp add: fun_eq_iff split_def)
  have init_some: "\<exists>r0 :: int. ?Init s = Some r0 \<and> (r0 \<noteq> 0 \<longrightarrow> 0 < limit)"
  proof (cases "0 < limit")
    case True
    have va0: "ptr_valid (heap_typing s) (a_buf +\<^sub>p uint a_pos)"
      using VA[of 0] True by simp
    have vb0: "ptr_valid (heap_typing s) (b_buf +\<^sub>p uint b_pos)"
      using VB[of 0] True by simp
    show ?thesis
      using True va0 vb0
      by (auto simp: ocondition_def obind_def oreturn_def ogets_def
                     oguard_def K_def)
  next
    case False
    then show ?thesis
      by (auto simp: ocondition_def oreturn_def K_def)
  qed
  obtain r0 :: int where r0_some: "?Init s = Some r0"
    and r0_lt: "r0 \<noteq> 0 \<longrightarrow> 0 < limit"
    using init_some by blast
  have loop_not_none: "owhile ?C ?B (0, r0) s \<noteq> None"
  proof (rule Reader_Monad.owhile_rule[
      where I = ?I
        and M = "measure (\<lambda>(n :: 32 word, ret :: int).
          unat limit - unat n)"])
    show "?I (0, r0) s"
      using r0_lt by simp
  next
    show "wf (measure (\<lambda>(n :: 32 word, ret :: int).
          unat limit - unat n))"
      by simp
  next
    fix r r' :: "32 word \<times> int"
    assume inv: "?I r s" and cond: "?C r s" and body: "?B r s = Some r'"
    obtain n ret where r_eq: "r = (n, ret)" by (cases r) auto
    obtain n' ret' where r'_eq: "r' = (n', ret')" by (cases r') auto
    have n_lt: "n < limit" using inv cond r_eq by simp
    have n_suc: "unat (n + 1) = Suc (unat n)"
      by (rule unat_suc_word_less[OF n_lt])
    have n'_eq: "n' = n + 1"
      using body r_eq r'_eq
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits)
    have n_lt_nat: "unat n < unat limit"
      using n_lt by (simp add: word_less_nat_alt)
    show "(r', r) \<in> measure (\<lambda>(n :: 32 word, ret :: int).
          unat limit - unat n)"
      using r_eq r'_eq n'_eq n_suc n_lt_nat by simp
  next
    fix r r' :: "32 word \<times> int"
    assume inv: "?I r s" and cond: "?C r s" and body: "?B r s = Some r'"
    obtain n ret where r_eq: "r = (n, ret)" by (cases r) auto
    obtain n' ret' where r'_eq: "r' = (n', ret')" by (cases r') auto
    have ret'_lt: "ret' \<noteq> 0 \<longrightarrow> n' < limit"
      using body r_eq r'_eq
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits)
    show "?I r' s"
      using ret'_lt r'_eq by simp
  next
    fix r :: "32 word \<times> int"
    assume inv: "?I r s" and cond: "?C r s" and body: "?B r s = None"
    obtain n ret where r_eq: "r = (n, ret)" by (cases r) auto
    have cond_lt: "n + 1 < limit"
      and guard_fail:
        "\<not> (IS_VALID(8 word) s (b_buf +\<^sub>p uint (b_pos + (n + 1))) \<and>
            IS_VALID(8 word) s (a_buf +\<^sub>p uint (a_pos + (n + 1))))"
      using body r_eq
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits)
    have False
      using guard_fail VA[OF cond_lt] VB[OF cond_lt] by simp
    thus "None \<noteq> (None :: (32 word \<times> int) option)" by simp
  next
    fix r :: "32 word \<times> int"
    assume "?I r s" and "\<not> ?C r s"
    show "Some r \<noteq> None" by simp
  qed
  obtain n' ret' where loop_some: "owhile ?C ?B (0, r0) s = Some (n', ret')"
    using loop_not_none by (cases "owhile ?C ?B (0, r0) s") auto
  show ?thesis
    using unfolded r0_some loop_some
    by (auto simp: obind_def oreturn_def K_def)
qed

lemma find_best_match'_isSome:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len tp :: "32 word"
  assumes rel:
    "source_index_heap_rel s (heap_bytes s src (unat src_len))
      head_arr next_arr"
      and nexts_wf:
    "source_index_heap_nexts_wf s (heap_bytes s src (unat src_len)) next_arr"
      and tp_le: "tp \<le> tgt_len"
      and src_valid: "buf_valid s src (unat src_len)"
      and tgt_valid: "buf_valid s tgt (unat tgt_len)"
      and head_valid:
        "\<And>h. h < hash_size \<Longrightarrow>
          ptr_valid (heap_typing s) (head_arr +\<^sub>p int h)"
      and next_valid:
        "\<And>p. p < unat src_len \<Longrightarrow>
          ptr_valid (heap_typing s) (next_arr +\<^sub>p int p)"
  shows "\<exists>m. find_best_match' src src_len tgt tgt_len tp head_arr next_arr s
          = Some m"
proof (cases "src_len < 4 \<or> tgt_len - tp < 4")
  case True
  then show ?thesis
    unfolding find_best_match'_def
    by (auto simp: ocondition_def oreturn_def K_def)
next
  case not_early: False
  let ?src_bytes = "heap_bytes s src (unat src_len)"
  let ?tgt_bytes = "heap_bytes s tgt (unat tgt_len)"
  let ?cand_ok = "\<lambda>cand :: 32 word.
    cand = no_entry32 \<or> unat cand + min_match \<le> length ?src_bytes"
  have src_len_word_le:
    "length ?src_bytes \<le> unat (no_entry32 :: 32 word)"
    using unat_lt2p[of src_len] by simp
  have rel_from:
    "source_index_heap_rel_from s ?src_bytes 0 head_arr next_arr"
    using rel by (simp add: source_index_heap_rel_from_0)
  have initial_cand_ok:
    "\<And>hv :: 32 word.
      heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)) = no_entry32 \<or>
      unat (heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF))) + min_match
        \<le> length ?src_bytes"
  proof -
    fix hv :: "32 word"
    let ?h = "unat (hv && 0xFFFF)"
    have h_lt: "?h < hash_size"
      by (rule hash_mask_word_unat_lt_hash_size)
    have head_ok_int:
      "heap_w32 s (head_arr +\<^sub>p int ?h) = no_entry32 \<or>
       unat (heap_w32 s (head_arr +\<^sub>p int ?h)) + min_match \<le> length ?src_bytes"
      by (rule source_index_heap_rel_from_head_wf[
          OF rel_from h_lt src_len_word_le])
    have heap_eq:
      "heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)) =
       heap_w32 s (head_arr +\<^sub>p int ?h)"
      by (simp only: uint_nat)
    show "heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)) = no_entry32 \<or>
      unat (heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF))) + min_match
        \<le> length ?src_bytes"
      using head_ok_int by (simp only: heap_eq)
  qed
  have next_cand_ok:
    "\<And>cand. \<lbrakk>?cand_ok cand; cand \<noteq> no_entry32\<rbrakk> \<Longrightarrow>
      ?cand_ok (heap_w32 s (next_arr +\<^sub>p uint cand))"
  proof -
    fix cand :: "32 word"
    assume cand_ok: "?cand_ok cand"
    assume cand_not_noentry: "cand \<noteq> no_entry32"
    have cand_match: "unat cand + min_match \<le> length ?src_bytes"
      using cand_ok cand_not_noentry by simp
    have next_ok_int:
      "heap_w32 s (next_arr +\<^sub>p int (unat cand)) = no_entry32 \<or>
       unat (heap_w32 s (next_arr +\<^sub>p int (unat cand))) + min_match
          \<le> length ?src_bytes"
      by (rule source_index_heap_nexts_wfD[OF nexts_wf cand_match])
    have heap_eq:
      "heap_w32 s (next_arr +\<^sub>p uint cand) =
       heap_w32 s (next_arr +\<^sub>p int (unat cand))"
      by (simp only: uint_nat)
    show "?cand_ok (heap_w32 s (next_arr +\<^sub>p uint cand))"
      using next_ok_int by (simp only: heap_eq)
  qed
  \<comment> \<open>hash4' is defined at tp\<close>
  have tgt_not_early_nat: "unat tp + min_match \<le> length ?tgt_bytes"
    using find_best_match'_not_early_tgt_bound[OF tp_le not_early] by simp
  have tgt_len32: "length ?tgt_bytes < 2 ^ 32"
    using unat_lt2p[of tgt_len] by simp
  have hash_valid: "\<And>k. k < min_match \<Longrightarrow>
      ptr_valid (heap_typing s) (tgt +\<^sub>p uint (tp + of_nat k :: 32 word))"
  proof -
    fix k
    assume k_lt: "k < min_match"
    have k_nat: "unat tp + k < unat tgt_len"
      using tgt_not_early_nat k_lt by simp
    have no32: "unat tp + k < 2 ^ 32"
      using k_nat unat_lt2p[of tgt_len] by simp
    have unat_eq: "unat (tp + of_nat k :: 32 word) = unat tp + k"
      using no32 by (simp add: unat_word_ariths unat_of_nat_eq)
    have lt: "unat (tp + of_nat k :: 32 word) < unat tgt_len"
      using unat_eq k_nat by simp
    show "ptr_valid (heap_typing s) (tgt +\<^sub>p uint (tp + of_nat k :: 32 word))"
      by (rule buf_valid_uintD[OF tgt_valid lt])
  qed
  have hash_some:
    "hash4' tgt tp s = Some (of_nat (hash4_spec ?tgt_bytes (unat tp)) :: 32 word)"
    apply (rule hash4'_heap_bytes[OF refl tgt_not_early_nat tgt_len32])
    using hash_valid by simp
  let ?hv = "of_nat (hash4_spec ?tgt_bytes (unat tp)) :: 32 word"
  let ?cand0 = "heap_w32 s (head_arr +\<^sub>p uint (?hv && 0xFFFF))"
  have head_ptr_ok:
    "ptr_valid (heap_typing s) (head_arr +\<^sub>p uint (?hv && 0xFFFF))"
  proof -
    have h_lt: "unat (?hv && 0xFFFF) < hash_size"
      by (rule hash_mask_word_unat_lt_hash_size)
    show ?thesis
      using head_valid[OF h_lt] by (simp only: uint_nat)
  qed
  let ?C = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word) s.
      cand \<noteq> no_entry32 \<and> checked < 0x10"
  let ?B = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word).
      do {
        (best_len, best_pos) <-
          ocondition (\<lambda>s. cand + 4 \<le> src_len)
            (do {
              l <- common_prefix' src cand src_len tgt tp tgt_len;
              oreturn
                (if 4 \<le> l \<and> best_len < l then (l, cand)
                 else (best_len, best_pos))
            })
            (oreturn (best_len, best_pos));
        oguard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint cand));
        ogets
          (\<lambda>s. (best_len, best_pos,
                heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1))
      }"
  let ?I = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word) (s :: lifted_globals).
      ?cand_ok cand"
  have loop_not_none:
    "owhile ?C ?B (0, 0, ?cand0, 0) s \<noteq> None"
  proof (rule Reader_Monad.owhile_rule[
      where I = ?I
        and M = "measure
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
               cand :: 32 word, checked :: 32 word). 16 - unat checked)"])
    show "?I (0, 0, ?cand0, 0) s"
      using initial_cand_ok[of ?hv] by simp
  next
    show "wf (measure
      (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
          cand :: 32 word, checked :: 32 word). 16 - unat checked))"
      by simp
  next
    fix r r' :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    assume inv: "?I r s" and cond: "?C r s" and body: "?B r s = Some r'"
    obtain bl bp cand checked where r_eq: "r = (bl, bp, cand, checked)"
      by (cases r) auto
    obtain bl' bp' cand' checked' where r'_eq: "r' = (bl', bp', cand', checked')"
      by (cases r') auto
    have checked'_eq: "checked' = checked + 1"
      using body r_eq r'_eq
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits option.splits)
    have checked_lt: "checked < 0x10"
      using cond r_eq by simp
    have checked_lt_nat: "unat checked < 16"
      using checked_lt by (simp add: word_less_nat_alt)
    have suc: "unat (checked + 1) = Suc (unat checked)"
      by (rule unat_suc_word_less[OF checked_lt])
    show "(r', r) \<in> measure
        (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
            cand :: 32 word, checked :: 32 word). 16 - unat checked)"
      using r_eq r'_eq checked'_eq suc checked_lt_nat by simp
  next
    fix r r' :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    assume inv: "?I r s" and cond: "?C r s" and body: "?B r s = Some r'"
    obtain bl bp cand checked where r_eq: "r = (bl, bp, cand, checked)"
      by (cases r) auto
    obtain bl' bp' cand' checked' where r'_eq: "r' = (bl', bp', cand', checked')"
      by (cases r') auto
    have cand_ok: "?cand_ok cand" using inv r_eq by simp
    have cand_ne: "cand \<noteq> no_entry32" using cond r_eq by simp
    have cand'_eq: "cand' = heap_w32 s (next_arr +\<^sub>p uint cand)"
      using body r_eq r'_eq
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits option.splits)
    show "?I r' s"
      using next_cand_ok[OF cand_ok cand_ne] cand'_eq r'_eq by simp
  next
    fix r :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    assume inv: "?I r s" and cond: "?C r s" and body: "?B r s = None"
    obtain bl bp cand checked where r_eq: "r = (bl, bp, cand, checked)"
      by (cases r) auto
    have cand_ok: "?cand_ok cand" using inv r_eq by simp
    have cand_ne: "cand \<noteq> no_entry32" using cond r_eq by simp
    have cand_match: "unat cand + min_match \<le> length ?src_bytes"
      using cand_ok cand_ne by simp
    have cand_nat_lt: "unat cand < unat src_len"
      using cand_match by (simp add: min_match_def)
    have next_ok:
      "ptr_valid (heap_typing s) (next_arr +\<^sub>p uint cand)"
      using next_valid[OF cand_nat_lt] by (simp only: uint_nat)
    have cand_le_w: "cand \<le> src_len"
      using cand_nat_lt by (simp add: word_le_nat_alt)
    obtain l where cp_some:
      "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
      using common_prefix'_isSome[OF src_valid tgt_valid cand_le_w tp_le]
      by blast
    have False
      using body r_eq cp_some next_ok
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits option.splits)
    thus "None \<noteq> (None :: (32 word \<times> 32 word \<times> 32 word \<times> 32 word) option)"
      by simp
  next
    fix r :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    assume "?I r s" and "\<not> ?C r s"
    show "Some r \<noteq> None" by simp
  qed
  obtain bl bp cand checked where loop_some:
    "owhile ?C ?B (0, 0, ?cand0, 0) s = Some (bl, bp, cand, checked)"
    using loop_not_none
    by (cases "owhile ?C ?B (0, 0, ?cand0, 0) s") auto
  have unfolded:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      (do {
         hv <- hash4' tgt tp;
         oguard (\<lambda>sb. IS_VALID(32 word) sb
             (head_arr +\<^sub>p uint (hv && 0xFFFF)));
         cand0 <- ogets (\<lambda>s. heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)));
         (best_len, best_pos, cand, checked) <-
           owhile ?C ?B (0, 0, cand0, 0);
         oreturn (match_t_C best_pos best_len)
       }) s"
    using not_early
    unfolding find_best_match'_def
    by (simp add: fun_eq_iff split_def ocondition_def K_def)
  show ?thesis
    using unfolded hash_some head_ptr_ok loop_some
    by (auto simp: obind_def oreturn_def ogets_def oguard_def K_def)
qed

text \<open>At loop exit the remaining fuel of the semantic budget is one, so a
  single flush reaches the final spec state.\<close>

lemma encode_window_section_budget_exit_flush:
  assumes budget:
    "encode_window_section_budget src_bytes tgt_bytes
      data_cap inst_cap addr_cap spec_st"
      and tp_ge: "length tgt_bytes \<le> enc_tp spec_st"
  shows "flush_pending_spec (length src_bytes) spec_st =
         encode_window_final_spec_state src_bytes tgt_bytes"
proof -
  have reaches:
    "encode_window_full_loop (length tgt_bytes + 1 - enc_tp spec_st)
       src_bytes tgt_bytes (build_index_spec src_bytes) spec_st =
     encode_window_final_spec_state src_bytes tgt_bytes"
    using budget
    by (simp add: encode_window_section_budget_def
        encode_window_spec_reaches_final_def)
  show ?thesis
  proof (cases "length tgt_bytes + 1 - enc_tp spec_st")
    case 0
    then show ?thesis
      using reaches tp_ge by (simp add: linorder_not_less)
  next
    case (Suc n)
    then show ?thesis
      using reaches tp_ge by (simp add: linorder_not_less)
  qed
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
      and final_caps:
    "encoder_final_section_caps_ok src_bytes tgt_bytes
      data_cap inst_cap addr_cap"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and head_valid:
        "\<And>h. h < hash_size \<Longrightarrow>
          ptr_valid (heap_typing s0) (head_arr +\<^sub>p int h)"
      and next_valid:
        "\<And>p. p < unat src_len \<Longrightarrow>
          ptr_valid (heap_typing s0) (next_arr +\<^sub>p int p)"
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
proof -
  let ?INV = "\<lambda>(pend_len :: 32 word) (sec :: sections_t_C) (tp :: 32 word)
                (t :: lifted_globals).
      (\<exists>spec_st. encode_window_loop_budget_rel t src src_len tgt tgt_len
          data data_cap inst inst_cap addr addr_cap pending pending_cap
          sec tp pend_len src_bytes tgt_bytes spec_st) \<and>
      encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
        src_bytes tgt_bytes"
  let ?I = "\<lambda>(r :: (sections_t_C option,
                    32 word \<times> sections_t_C \<times> 32 word) exception_or_result)
              (t :: lifted_globals).
      (\<forall>e :: sections_t_C. r \<noteq> Exn e) \<and>
      (\<forall>pend_len sec tp. r = Result (pend_len, sec, tp) \<longrightarrow>
         ?INV pend_len sec tp t)"
  let ?R = "measure
      (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word),
         _ :: lifted_globals). unat tgt_len - unat tp)"
  have loop_buffers0:
    "encode_window_loop_buffers_ok s0 src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    by (rule encoder_buffers_ok_encode_window_loop_buffers_ok[OF buffers])
  have body_step:
    "\<And>pend_len sec tp t.
      ?INV pend_len sec tp t \<Longrightarrow> tp < tgt_len \<Longrightarrow>
      encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> t
      \<lbrace> \<lambda>r u. ?I r u \<and>
           (\<forall>b. r = Result b \<longrightarrow>
              ((b, u), ((pend_len, sec, tp), t)) \<in> ?R) \<rbrace>"
  proof -
    fix pend_len sec tp t
    assume inv: "?INV pend_len sec tp t" and tp_lt: "tp < tgt_len"
    obtain spec_st where budget_t:
      "encode_window_loop_budget_rel t src src_len tgt tgt_len
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        sec tp pend_len src_bytes tgt_bytes spec_st"
      using inv by blast
    have index_t:
      "encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
        src_bytes tgt_bytes"
      using inv by blast
    have typing_t: "heap_typing t = heap_typing s0"
      using index_t by (simp add: encoder_index_post_def)
    have buffers_t:
      "encode_window_loop_buffers_ok t src src_len tgt tgt_len
        pending pending_cap data data_cap inst inst_cap addr addr_cap"
      by (rule encode_window_loop_buffers_ok_heap_typing[
            OF loop_buffers0 typing_t])
    have match_rel_t:
      "encode_window_match_rel t src src_len tgt tgt_len head_arr next_arr
        src_bytes tgt_bytes"
      by (rule encoder_index_post_encode_window_match_rel[OF buffers index_t])
    have pending_len_t: "length (enc_pending spec_st) = unat pend_len"
      and tp_eq_t: "enc_tp spec_st = unat tp"
      and flushed_inv_t:
        "enc_flushed spec_st + length (enc_pending spec_st) = enc_tp spec_st"
      using budget_t by (simp_all add: encode_window_loop_budget_rel_def)
    have tgt_pending_cap: "unat tgt_len \<le> unat pending_cap"
      using buffers_t by (simp add: encode_window_loop_buffers_ok_def)
    have pend_lt: "pend_len < pending_cap"
    proof -
      have "unat pend_len \<le> unat tp"
        using pending_len_t flushed_inv_t tp_eq_t by linarith
      also have "... < unat tgt_len"
        using tp_lt by (simp add: word_less_nat_alt)
      also have "... \<le> unat pending_cap"
        by (rule tgt_pending_cap)
      finally show ?thesis by (simp add: word_less_nat_alt)
    qed
    have src_valid_t: "buf_valid t src (unat src_len)"
      and tgt_valid_t: "buf_valid t tgt (unat tgt_len)"
      using buffers_t by (simp_all add: encode_window_loop_buffers_ok_def)
    have rel_t:
      "source_index_heap_rel t (heap_bytes t src (unat src_len))
        head_arr next_arr"
      using index_t by (simp add: encoder_index_post_def)
    have nexts_wf_t:
      "source_index_heap_nexts_wf t (heap_bytes t src (unat src_len))
        next_arr"
      using index_t by (simp add: encoder_index_post_def)
    have exm:
      "\<exists>m. find_best_match' src src_len tgt tgt_len tp head_arr next_arr t =
        Some m"
    proof (rule find_best_match'_isSome[OF rel_t nexts_wf_t _ src_valid_t
        tgt_valid_t])
      show "tp \<le> tgt_len" using tp_lt by simp
    next
      fix h assume "h < hash_size"
      then show "ptr_valid (heap_typing t) (head_arr +\<^sub>p int h)"
        using head_valid typing_t by simp
    next
      fix p assume "p < unat src_len"
      then show "ptr_valid (heap_typing t) (next_arr +\<^sub>p int p)"
        using next_valid typing_t by simp
    qed
    have total:
      "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> t
      \<lbrace> \<lambda>r u. \<exists>sec' tp' pend_len' spec_st'.
           r = Result (pend_len', sec', tp') \<and>
           encode_window_loop_budget_rel u src src_len tgt tgt_len
             data data_cap inst inst_cap addr addr_cap pending pending_cap
             sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
           enc_tp spec_st < enc_tp spec_st' \<and>
           (((pend_len', sec', tp'), u), ((pend_len, sec, tp), t)) \<in>
             measure
               (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                  unat tgt_len - unat tp) \<rbrace>"
      by (rule encode_window_loop_body_topdown[
            OF budget_t match_rel_t buffers_t src_tgt_bound pend_lt tp_lt
               exm])
    have frame:
      "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> t
      ?\<lbrace> \<lambda>r u. heap_w32 u = heap_w32 t \<and>
              heap_typing u = heap_typing t \<rbrace>"
      by (rule encode_window_c_loop_body_w32_typing_frame)
    have partial_conj:
      "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> t
      ?\<lbrace> \<lambda>r u. (\<exists>sec' tp' pend_len' spec_st'.
           r = Result (pend_len', sec', tp') \<and>
           encode_window_loop_budget_rel u src src_len tgt tgt_len
             data data_cap inst inst_cap addr addr_cap pending pending_cap
             sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
           enc_tp spec_st < enc_tp spec_st' \<and>
           (((pend_len', sec', tp'), u), ((pend_len, sec, tp), t)) \<in>
             measure
               (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                  unat tgt_len - unat tp)) \<and>
           (heap_w32 u = heap_w32 t \<and>
            heap_typing u = heap_typing t) \<rbrace>"
      by (rule runs_to_partial_conj[OF runs_to_partial_of_runs_to[OF total]
            frame])
    have both:
      "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> t
      \<lbrace> \<lambda>r u. (\<exists>sec' tp' pend_len' spec_st'.
           r = Result (pend_len', sec', tp') \<and>
           encode_window_loop_budget_rel u src src_len tgt tgt_len
             data data_cap inst inst_cap addr addr_cap pending pending_cap
             sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
           enc_tp spec_st < enc_tp spec_st' \<and>
           (((pend_len', sec', tp'), u), ((pend_len, sec, tp), t)) \<in>
             measure
               (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                  unat tgt_len - unat tp)) \<and>
           (heap_w32 u = heap_w32 t \<and>
            heap_typing u = heap_typing t) \<rbrace>"
      by (rule runs_to_of_runs_to_partial_runs_to'[OF total partial_conj])
    show "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        (pend_len, sec, tp) \<bullet> t
      \<lbrace> \<lambda>r u. ?I r u \<and>
           (\<forall>b. r = Result b \<longrightarrow>
              ((b, u), ((pend_len, sec, tp), t)) \<in> ?R) \<rbrace>"
    proof (rule runs_to_weaken[OF both])
      fix r :: "(sections_t_C option,
                 32 word \<times> sections_t_C \<times> 32 word) exception_or_result"
        and u :: lifted_globals
      assume H: "(\<exists>sec' tp' pend_len' spec_st'.
           r = Result (pend_len', sec', tp') \<and>
           encode_window_loop_budget_rel u src src_len tgt tgt_len
             data data_cap inst inst_cap addr addr_cap pending pending_cap
             sec' tp' pend_len' src_bytes tgt_bytes spec_st' \<and>
           enc_tp spec_st < enc_tp spec_st' \<and>
           (((pend_len', sec', tp'), u), ((pend_len, sec, tp), t)) \<in>
             measure
               (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                  unat tgt_len - unat tp)) \<and>
           (heap_w32 u = heap_w32 t \<and>
            heap_typing u = heap_typing t)"
      obtain sec' tp' pend_len' spec_st' where
          r_def: "r = Result (pend_len', sec', tp')"
        and budget_u:
          "encode_window_loop_budget_rel u src src_len tgt tgt_len
            data data_cap inst inst_cap addr addr_cap pending pending_cap
            sec' tp' pend_len' src_bytes tgt_bytes spec_st'"
        and meas:
          "(((pend_len', sec', tp'), u), ((pend_len, sec, tp), t)) \<in>
             measure
               (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                  unat tgt_len - unat tp)"
        and w32_u: "heap_w32 u = heap_w32 t"
        and typing_u: "heap_typing u = heap_typing t"
        using H by blast
      have src_u: "heap_bytes u src (unat src_len) = src_bytes"
        and tgt_u: "heap_bytes u tgt (unat tgt_len) = tgt_bytes"
        using budget_u by (simp_all add: encode_window_loop_budget_rel_def)
      have index_u:
        "encoder_index_post s0 u src src_len tgt tgt_len head_arr next_arr
          src_bytes tgt_bytes"
        by (rule encoder_index_post_w32_typing_transport[
              OF index_t w32_u typing_u src_u tgt_u])
      show "?I r u \<and>
           (\<forall>b. r = Result b \<longrightarrow>
              ((b, u), ((pend_len, sec, tp), t)) \<in> ?R)"
        using r_def budget_u index_u meas by auto
    qed
  qed
  show ?thesis
  proof (rule runs_to_whileLoop_exn'[where R = ?R and I = ?I])
    fix a :: "32 word \<times> sections_t_C \<times> 32 word" and t
    assume I_a: "?I (Result a) t"
      and C_a: "(case a of (pend_len, sec, tp) \<Rightarrow> \<lambda>s. tp < tgt_len) t"
    obtain pend_len sec tp where a_eq: "a = (pend_len, sec, tp)"
      by (cases a) auto
    have inv: "?INV pend_len sec tp t"
      using I_a a_eq by simp
    have tp_lt: "tp < tgt_len"
      using C_a a_eq by simp
    show "encode_window_c_loop_body src src_len tgt tgt_len head_arr next_arr
        data data_cap inst inst_cap addr addr_cap pending pending_cap a
        \<bullet> t
      \<lbrace> \<lambda>r u. ?I r u \<and> (\<forall>b. r = Result b \<longrightarrow> ((b, u), (a, t)) \<in> ?R) \<rbrace>"
      using body_step[OF inv tp_lt] a_eq by simp
  next
    fix a :: "32 word \<times> sections_t_C \<times> 32 word" and t
    assume I_a: "?I (Result a) t"
      and nC_a: "\<not> (case a of (pend_len, sec, tp) \<Rightarrow> \<lambda>s. tp < tgt_len) t"
    obtain pend_len sec tp where a_eq: "a = (pend_len, sec, tp)"
      by (cases a) auto
    have inv: "?INV pend_len sec tp t"
      using I_a a_eq by simp
    have tp_ge: "\<not> tp < tgt_len"
      using nC_a a_eq by simp
    obtain spec_st where budget_t:
      "encode_window_loop_budget_rel t src src_len tgt tgt_len
        data data_cap inst inst_cap addr addr_cap pending pending_cap
        sec tp pend_len src_bytes tgt_bytes spec_st"
      using inv by blast
    have index_t:
      "encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
        src_bytes tgt_bytes"
      using inv by blast
    have budget0:
      "encode_window_section_budget src_bytes tgt_bytes
        data_cap inst_cap addr_cap spec_st"
      and tp_eq: "enc_tp spec_st = unat tp"
      and tgt_len_eq: "length tgt_bytes = unat tgt_len"
      using budget_t by (simp_all add: encode_window_loop_budget_rel_def)
    have tp_ge_nat: "length tgt_bytes \<le> enc_tp spec_st"
      using tp_ge tp_eq tgt_len_eq by (simp add: word_less_nat_alt)
    have flush_eq:
      "flush_pending_spec (length src_bytes) spec_st =
        encode_window_final_spec_state src_bytes tgt_bytes"
      by (rule encode_window_section_budget_exit_flush[OF budget0 tp_ge_nat])
    show "\<exists>pend_len sec tp spec_st.
        Result a = Result (pend_len, sec, tp) \<and>
        \<not> tp < tgt_len \<and>
        encode_window_loop_budget_rel t src src_len tgt tgt_len
          data data_cap inst inst_cap addr addr_cap pending pending_cap
          sec tp pend_len src_bytes tgt_bytes spec_st \<and>
        flush_pending_spec (length src_bytes) spec_st =
          encode_window_final_spec_state src_bytes tgt_bytes \<and>
        encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
          src_bytes tgt_bytes"
      using a_eq tp_ge budget_t flush_eq index_t by blast
  next
    fix a :: sections_t_C and t
    assume "?I (Exn a) t"
    then show "\<exists>pend_len sec tp spec_st.
        Exn a = Result (pend_len, sec, tp) \<and>
        \<not> tp < tgt_len \<and>
        encode_window_loop_budget_rel t src src_len tgt tgt_len
          data data_cap inst inst_cap addr addr_cap pending pending_cap
          sec tp pend_len src_bytes tgt_bytes spec_st \<and>
        flush_pending_spec (length src_bytes) spec_st =
          encode_window_final_spec_state src_bytes tgt_bytes \<and>
        encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
          src_bytes tgt_bytes"
      by simp
  next
    show "wf ?R" by simp
  next
    show "?I (Result (0, sec0, 0)) s"
      using init index by auto
  qed
qed

text \<open>The final flush under the budget invariant: at loop exit the retained
  data/inst linear slacks fund the flush (tp = tgt_len releases the whole
  window term), the addr section is untouched, and the flushed spec state
  is exactly the final one.\<close>

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
proof -
  let ?final = "encode_window_final_spec_state src_bytes tgt_bytes"
  have typing_s: "heap_typing s = heap_typing s0"
    using index by (simp add: encoder_index_post_def)
  have loop_buffers0:
    "encode_window_loop_buffers_ok s0 src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    by (rule encoder_buffers_ok_encode_window_loop_buffers_ok[OF buffers])
  have buffers_s:
    "encode_window_loop_buffers_ok s src src_len tgt tgt_len
      pending pending_cap data data_cap inst inst_cap addr addr_cap"
    by (rule encode_window_loop_buffers_ok_heap_typing[
          OF loop_buffers0 typing_s])
  have sections_rel: "enc_sections_state_rel s data inst addr sec spec_st"
    and sec_ok: "sections_t_C.err_C sec = ENC_OK"
    and pending_heap:
      "heap_bytes_word s pending 0 pend_len = enc_pending spec_st"
    and pending_len: "length (enc_pending spec_st) = unat pend_len"
    and tp_eq: "enc_tp spec_st = unat tp"
    and tgt_len_eq: "length tgt_bytes = unat tgt_len"
    and pend_cap_le: "unat pend_len \<le> unat pending_cap"
    and tp_le: "unat tp \<le> unat tgt_len"
    and abs: "enc_cache_abs s (enc_cache spec_st)"
    and cwf: "enc_cache_wf (enc_cache spec_st)"
    using loop_exit by (simp_all add: encode_window_loop_budget_rel_def)
  have data_slack:
    "unat (sections_t_C.data_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat data_cap"
    using loop_exit unfolding encode_window_loop_budget_rel_def by blast
  have inst_slack:
    "unat (sections_t_C.inst_pos_C sec) + unat pend_len +
       (unat tgt_len - unat tp) + 64 \<le> unat inst_cap"
    using loop_exit unfolding encode_window_loop_budget_rel_def by blast
  have dp_len0: "length (enc_data spec_st) = unat (sections_t_C.data_pos_C sec)"
    and ip_len0: "length (enc_inst spec_st) = unat (sections_t_C.inst_pos_C sec)"
    and ap_len0: "length (enc_addr spec_st) = unat (sections_t_C.addr_pos_C sec)"
    using enc_sections_state_rel_lengths[OF sections_rel] by simp_all
  have final_data_cap: "length (enc_data ?final) \<le> unat data_cap"
    and final_inst_cap: "length (enc_inst ?final) \<le> unat inst_cap"
    and final_addr_cap: "length (enc_addr ?final) \<le> unat addr_cap"
    using final_caps by (simp_all add: encoder_final_section_caps_ok_def)
  have pending_lt32: "length (enc_pending spec_st) < 2 ^ 32"
    using pending_len unat_lt2p[of pend_len] by simp
  have flush_data_room64:
    "length (enc_data (flush_pending_spec (length src_bytes) spec_st)) + 64
      \<le> unat data_cap"
    using flush_pending_spec_growth_bounds(1)[OF pending_lt32,
        of "length src_bytes"]
      pending_len dp_len0 data_slack
    by linarith
  have flush_inst_room64:
    "length (enc_inst (flush_pending_spec (length src_bytes) spec_st)) + 64
      \<le> unat inst_cap"
    using flush_pending_spec_growth_bounds(2)[OF pending_lt32,
        of "length src_bytes"]
      pending_len ip_len0 inst_slack
    by linarith
  have flush_addr_room:
    "length (enc_addr (flush_pending_spec (length src_bytes) spec_st))
      \<le> unat addr_cap"
    using final_spec final_addr_cap by simp
  have cond_flush:
    "condition (\<lambda>s. 0 < pend_len)
       (flush_pending' sec data data_cap inst inst_cap pending pend_len)
       (return sec) \<bullet> s
     \<lbrace> \<lambda>Res sec' t.
          enc_sections_state_rel t data inst addr sec' ?final \<and>
          sections_t_C.err_C sec' = ENC_OK \<and>
          heap_typing t = heap_typing s \<rbrace>"
  proof (cases "0 < pend_len")
    case pend_pos: True
    have FH:
      "flush_pending' sec data data_cap inst inst_cap pending pend_len \<bullet> s
       \<lbrace> \<lambda>r t. \<exists>sec'.
            r = Result sec' \<and>
            enc_sections_state_rel t data inst addr sec'
              (flush_pending_spec (length src_bytes) spec_st) \<and>
            sections_t_C.err_C sec' = ENC_OK \<and>
            heap_bytes_word t src 0 src_len =
              heap_bytes_word s src 0 src_len \<and>
            heap_bytes_word t tgt 0 tgt_len =
              heap_bytes_word s tgt 0 tgt_len \<and>
            enc_cache_abs t (enc_cache spec_st) \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule flush_pending'_loop_from_final_fits_framed[
            OF buffers_s sections_rel abs cwf sec_ok pending_heap[symmetric]
               pend_cap_le flush_data_room64 flush_inst_room64
               flush_addr_room])
    show ?thesis
      unfolding condition_def
      using pend_pos
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF FH])
      using final_spec
      apply auto
      done
  next
    case False
    have pend0: "pend_len = 0"
      using False by (simp add: word_neq_0_conv not_less)
    have pending_nil: "enc_pending spec_st = []"
      using pending_len pend0 by simp
    have flush_secs:
      "enc_data (flush_pending_spec (length src_bytes) spec_st) =
        enc_data spec_st"
      "enc_inst (flush_pending_spec (length src_bytes) spec_st) =
        enc_inst spec_st"
      "enc_addr (flush_pending_spec (length src_bytes) spec_st) =
        enc_addr spec_st"
      using flush_pending_spec_empty_sections[OF pending_nil] by simp_all
    have final_secs:
      "enc_data ?final = enc_data spec_st"
      "enc_inst ?final = enc_inst spec_st"
      "enc_addr ?final = enc_addr spec_st"
      using flush_secs final_spec by simp_all
    have rel_final: "enc_sections_state_rel s data inst addr sec ?final"
      using sections_rel final_secs
      by (simp add: enc_sections_state_rel_def)
    show ?thesis
      unfolding condition_def
      using False rel_final sec_ok
      by runs_to_vcg
  qed
  show ?thesis
    apply (rule runs_to_weaken[
      OF runs_to_liftE_bind_throw_exn_result[OF cond_flush]])
    subgoal premises post for r t
    proof -
      obtain sec' where
          r_def: "r = Exn sec'"
        and rel_sec:
          "enc_sections_state_rel t data inst addr sec' ?final"
        and sec'_ok: "sections_t_C.err_C sec' = ENC_OK"
        and typing_t: "heap_typing t = heap_typing s"
        using post by auto
      have caps_e:
        "encoder_window_caps_ok sec' data_cap inst_cap addr_cap"
        using enc_sections_state_rel_lengths[OF rel_sec]
          final_data_cap final_inst_cap final_addr_cap
        by (auto simp: encoder_window_caps_ok_def)
      show ?thesis
        using r_def rel_sec sec'_ok caps_e typing_t by auto
    qed
    done
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
      and final_caps:
        "encoder_final_section_caps_ok src_bytes tgt_bytes
          data_cap inst_cap addr_cap"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and head_valid:
        "\<And>h. h < hash_size \<Longrightarrow>
          ptr_valid (heap_typing s0) (head_arr +\<^sub>p int h)"
      and next_valid:
        "\<And>p. p < unat src_len \<Longrightarrow>
          ptr_valid (heap_typing s0) (next_arr +\<^sub>p int p)"
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
        "encode_window_loop_budget_rel s_reset src src_len tgt tgt_len
          data data_cap inst inst_cap addr addr_cap pending pending_cap
          ?sec0 0 0 src_bytes tgt_bytes enc_full_init"
        by (rule encode_window_initial_loop_budget_rel[
            OF input loop_buffers_reset final_caps])
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
              encode_window_loop_budget_rel t src src_len tgt tgt_len
                data data_cap inst inst_cap addr addr_cap pending pending_cap
                sec tp pend_len src_bytes tgt_bytes spec_st \<and>
              flush_pending_spec (length src_bytes) spec_st =
                encode_window_final_spec_state src_bytes tgt_bytes \<and>
              encoder_index_post s0 t src src_len tgt tgt_len head_arr next_arr
                src_bytes tgt_bytes \<rbrace>"
	        by (rule encode_window_while_loop_topdown[
	            OF input buffers index_reset fit final_caps src_tgt_bound
	               head_valid next_valid init_rel])
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
            OF input buffers _ fit final_caps _ _ _]])
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
      and final_caps:
        "encoder_final_section_caps_ok src_bytes tgt_bytes
          data_cap inst_cap addr_cap"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and head_valid:
        "\<And>h. h < hash_size \<Longrightarrow>
          ptr_valid (heap_typing s0) (head_arr +\<^sub>p int h)"
      and next_valid:
        "\<And>p. p < unat src_len \<Longrightarrow>
          ptr_valid (heap_typing s0) (next_arr +\<^sub>p int p)"
  shows "encode_window' src src_len tgt tgt_len head_arr next_arr
            data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>sec.
	               r = Result sec \<and>
	               encoder_window_post t data inst addr sec src_bytes tgt_bytes \<and>
	               encoder_window_caps_ok sec data_cap inst_cap addr_cap \<and>
	               heap_typing t = heap_typing s \<rbrace>"
proof (rule runs_to_weaken[
    OF encode_window_phase_core_topdown[
      OF input buffers index fit final_caps src_tgt_bound
         head_valid next_valid]])
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
          OF input buffers index fit final_caps src_tgt_bound
             head_valid next_valid])
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
