theory VcdiffEnc_Emit
  imports
    VcdiffEnc_Wire
    VcdiffEnc_Cache_Opcode
begin

context vcdiff_enc_global_addresses begin

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

(* Nontrivial COPY/flush/fused preservation needs these shared facts:
   best_mode'_encode_address_correct for the C cache state,
   section_decodes_copy_append,
   section_decodes_flush_pending_add_run_chunks, and
   section_decodes_fused_add_copy_append. *)

end

end
