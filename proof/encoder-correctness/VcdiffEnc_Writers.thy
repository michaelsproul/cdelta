theory VcdiffEnc_Writers
  imports
    CdeltaEncoder.VcdiffEnc
    CdeltaSpecRoundtrip.Spec_Roundtrip
begin

context vcdiff_enc_global_addresses begin

abbreviation ENC_OK :: "32 word" where
  "ENC_OK \<equiv> 0"

abbreviation ENC_OVERFLOW :: "32 word" where
  "ENC_OVERFLOW \<equiv> 1"

definition wr_result :: "wr_t_C \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> bool" where
  "wr_result r pos err \<longleftrightarrow>
     wr_t_C.pos_C r = pos \<and> wr_t_C.err_C r = err"

lemma wr_resultD:
  assumes "wr_result r pos err"
  shows "wr_t_C.pos_C r = pos" "wr_t_C.err_C r = err"
  using assms by (simp_all add: wr_result_def)

definition sections_result ::
  "sections_t_C \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> bool" where
  "sections_result r data_pos inst_pos addr_pos err \<longleftrightarrow>
     sections_t_C.data_pos_C r = data_pos \<and>
     sections_t_C.inst_pos_C r = inst_pos \<and>
     sections_t_C.addr_pos_C r = addr_pos \<and>
     sections_t_C.err_C r = err"

lemma sections_resultD:
  assumes "sections_result r data_pos inst_pos addr_pos err"
  shows "sections_t_C.data_pos_C r = data_pos"
        "sections_t_C.inst_pos_C r = inst_pos"
        "sections_t_C.addr_pos_C r = addr_pos"
        "sections_t_C.err_C r = err"
  using assms by (simp_all add: sections_result_def)

lemma unat_add_of_nat_index:
  fixes base sz :: "32 word"
  assumes n_lt: "n < unat sz"
      and no_overflow: "unat base + unat sz < 2 ^ 32"
  shows "unat (base + of_nat n :: 32 word) = unat base + n"
proof -
  have n_lt32: "n < 2 ^ 32"
    using n_lt unat_lt2p[of sz] by simp
  have ofn: "unat (of_nat n :: 32 word) = n"
    using n_lt32 by (simp add: unat_of_nat_eq)
  have sum_lt: "unat base + n < 2 ^ 32"
    using n_lt no_overflow by simp
  show ?thesis
    using sum_lt ofn by (simp add: unat_word_ariths(1))
qed

lemma unat_word_add_no_overflow:
  fixes a b :: "32 word"
  assumes no_overflow: "unat a + unat b < 2 ^ 32"
  shows "unat (a + b) = unat a + unat b"
  using no_overflow by (simp add: unat_word_ariths(1))

lemma unat_word_suc_of_less:
  fixes pos cap :: "32 word"
  assumes pos_lt: "pos < cap"
  shows "unat (pos + 1) = Suc (unat pos)"
proof -
  have "unat pos + unat (1 :: 32 word) < 2 ^ 32"
    using pos_lt unat_lt2p[of cap] by (simp add: word_less_nat_alt)
  thus ?thesis
    using unat_word_add_no_overflow[of pos 1] by simp
qed

lemma unat_suc_le_of_word_less:
  fixes i len :: "32 word"
  assumes "i < len"
  shows "unat (i + 1) \<le> unat len"
  using assms by unat_arith

lemma unat_measure_decrease_of_word_less:
  fixes i len :: "32 word"
  assumes "i < len"
  shows "unat len - unat (i + 1) < unat len - unat i"
  using assms by unat_arith

lemma word32_shiftr7_decreases:
  fixes x :: "32 word"
  assumes "x \<noteq> 0"
  shows "unat (x >> (7 :: nat)) < unat x"
  using assms
  by (simp add: Word_Lemmas.shiftr_div_2n' word_neq_0_conv
                word_less_nat_alt Euclidean_Rings.div_less_dividend)

lemma word32_shiftr_35_zero:
  fixes x :: "32 word"
  shows "x >> (35 :: nat) = 0"
  by (rule Word_Lemmas.shiftr_eq_0) simp

lemma varint_shift_ok_of_unat_le5:
  fixes len i :: "32 word"
  assumes len_le: "unat len \<le> 5"
      and i_lt: "i < len"
  shows "7 * len - 7 - 7 * i < (0x20 :: 32 word)"
proof -
  have i_nat_lt: "unat i < unat len"
    using i_lt by (simp add: word_less_nat_alt)
  have len_mult: "unat (7 * len :: 32 word) = 7 * unat len"
    using len_le by (simp add: Word.unat_word_ariths)
  have i_mult: "unat (7 * i :: 32 word) = 7 * unat i"
    using len_le i_nat_lt by (simp add: Word.unat_word_ariths)
  have expr_unat:
    "unat (7 * len - 7 - 7 * i :: 32 word) =
     7 * unat len - 7 - 7 * unat i"
    using len_le i_nat_lt len_mult i_mult
    by (simp add: Word.unat_arith_simps)
  have "7 * unat len - 7 - 7 * unat i < 32"
    using len_le i_nat_lt by arith
  thus ?thesis
    using expr_unat by (simp add: word_less_nat_alt)
qed

lemma varint_size'_some_bounds:
  shows "\<exists>n. varint_size' v s = Some n \<and> 1 \<le> unat n \<and> unat n \<le> 5"
proof -
  let ?C = "\<lambda>(n :: 32 word, x :: 32 word) s. x \<noteq> 0"
  let ?B = "\<lambda>(n :: 32 word, x :: 32 word). oreturn (n + 1, x >> (7 :: nat))"
  let ?I = "\<lambda>(n :: 32 word, x :: 32 word) s.
       1 \<le> unat n \<and> unat n \<le> 5 \<and> x >> (7 * (5 - unat n)) = 0"
  have loop_bound:
    "case owhile ?C ?B (1, v >> (7 :: nat)) s of
       None \<Rightarrow> False
     | Some (n, x) \<Rightarrow> 1 \<le> unat n \<and> unat n \<le> 5"
    apply (rule Reader_Monad.owhile_rule[
      where I = ?I and M = "measure (\<lambda>(n :: 32 word, x :: 32 word). unat x)"])
         apply (simp add: Word_Lemmas.shiftr_shiftr word32_shiftr_35_zero)
        apply simp
    subgoal for r r'
      by (cases r; cases r')
         (auto simp: Reader_Monad.oreturn_apply
               intro: word32_shiftr7_decreases)
    subgoal for r r'
      apply (cases r; cases r')
      apply (clarsimp simp: Reader_Monad.oreturn_apply)
      apply (subgoal_tac "unat a < 5")
       apply (subgoal_tac "unat (a + 1) = unat a + 1")
        apply (simp add: Word_Lemmas.shiftr_shiftr algebra_simps)
       apply (simp add: Word.unat_arith_simps)
      apply (rule ccontr)
      apply simp
      done
    subgoal for r
      by (cases r) (simp add: Reader_Monad.oreturn_apply)
    subgoal for r
      by (cases r) simp
    done
  show ?thesis
    using loop_bound unfolding varint_size'_def
    by (auto simp: Reader_Monad.obind_def Reader_Monad.oreturn_apply
             split: option.splits prod.splits)
qed

lemma varint_size'_some:
  shows "\<exists>n. varint_size' v s = Some n"
  using varint_size'_some_bounds[of v s] by auto

lemma varint_size'_state_independent:
  "varint_size' v t = varint_size' v s"
  unfolding varint_size'_def
  by (simp add: Reader_Monad.owhile_def Reader_Monad.obind_def
                Reader_Monad.oreturn_def K_def split_beta case_prod_beta
          split: prod.splits option.splits)

lemma varint_size'_heap_w8_update[simp]:
  "varint_size' v (heap_w8_update f s) = varint_size' v s"
  by (rule varint_size'_state_independent)

lemma varint_size'_some_bounds_shift:
  shows "\<exists>n. varint_size' v s = Some n \<and>
             1 \<le> unat n \<and> unat n \<le> 5 \<and>
             v >> (7 * unat n) = 0"
proof -
  let ?C = "\<lambda>(n :: 32 word, x :: 32 word) s. x \<noteq> 0"
  let ?B = "\<lambda>(n :: 32 word, x :: 32 word). oreturn (n + 1, x >> (7 :: nat))"
  let ?I = "\<lambda>(n :: 32 word, x :: 32 word) s.
       1 \<le> unat n \<and> unat n \<le> 5 \<and>
       x >> (7 * (5 - unat n)) = 0 \<and>
       x = v >> (7 * unat n)"
  have loop_result:
    "case owhile ?C ?B (1, v >> (7 :: nat)) s of
       None \<Rightarrow> False
     | Some (n, x) \<Rightarrow>
         1 \<le> unat n \<and> unat n \<le> 5 \<and>
         v >> (7 * unat n) = 0"
    apply (rule Reader_Monad.owhile_rule[
      where I = ?I and M = "measure (\<lambda>(n :: 32 word, x :: 32 word). unat x)"])
         apply (simp add: Word_Lemmas.shiftr_shiftr word32_shiftr_35_zero)
        apply simp
    subgoal for r r'
      by (cases r; cases r')
         (auto simp: Reader_Monad.oreturn_apply
               intro: word32_shiftr7_decreases)
    subgoal for r r'
      apply (cases r; cases r')
      apply (clarsimp simp: Reader_Monad.oreturn_apply)
      apply (subgoal_tac "unat a < 5")
       apply (subgoal_tac "unat (a + 1) = unat a + 1")
        apply (subgoal_tac "7 + 7 * (5 - unat (a + 1)) = 7 * (5 - unat a)")
         apply (simp add: Word_Lemmas.shiftr_shiftr algebra_simps)
        apply arith
       apply (simp add: Word.unat_arith_simps)
      apply (rule ccontr)
      apply (simp add: word32_shiftr_35_zero)
      done
    subgoal for r
      by (cases r) (simp add: Reader_Monad.oreturn_apply)
    subgoal for r
      by (cases r) simp
    done
  show ?thesis
    using loop_result unfolding varint_size'_def
    by (auto simp: Reader_Monad.obind_def Reader_Monad.oreturn_apply
             split: option.splits prod.splits)
qed

lemma varint_size'_bounds:
  assumes "varint_size' v s = Some n"
  shows "1 \<le> unat n \<and> unat n \<le> 5"
  using varint_size'_some_bounds[of v s] assms by auto

lemma varint_size'_shiftr_zero:
  assumes "varint_size' v s = Some n"
  shows "v >> (7 * unat n) = 0"
  using varint_size'_some_bounds_shift[of v s] assms by auto

lemma varint_size'_ge1:
  assumes "varint_size' v s = Some n"
  shows "1 \<le> unat n"
  using varint_size'_bounds[OF assms] by simp

lemma varint_size'_le5:
  assumes "varint_size' v s = Some n"
  shows "unat n \<le> 5"
  using varint_size'_bounds[OF assms] by simp

lemma varint_size'_shift_ok:
  assumes size: "varint_size' v s = Some n"
      and i_lt: "i < n"
  shows "7 * n - 7 - 7 * i < (0x20 :: 32 word)"
  using varint_size'_le5[OF size] i_lt
  by (rule varint_shift_ok_of_unat_le5)

lemma unat_less_suc_word_le_len:
  fixes i len :: "32 word"
  assumes "i < len"
      and "k < unat (i + 1)"
  shows "k < unat len"
  using assms by unat_arith

lemma unat_less_suc_word_prevD:
  fixes i len :: "32 word"
  assumes "i < len"
      and "k < unat (i + 1)"
      and "k \<noteq> unat i"
  shows "k < unat i"
  using assms by unat_arith

lemma word_index_ptr_eq_currentD:
  fixes len pos i :: "32 word"
  assumes dst_inj: "\<forall>a < unat len. \<forall>b < unat len.
           a \<noteq> b \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat a) \<noteq>
           buf +\<^sub>p uint (pos + of_nat b)"
      and i_lt: "i < len"
      and k_lt: "k < unat (i + 1)"
      and ptr_eq:
        "buf +\<^sub>p uint (pos + of_nat k) =
         buf +\<^sub>p uint (pos + i)"
  shows "k = unat i"
proof (rule ccontr)
  assume k_ne: "k \<noteq> unat i"
  have k_len: "k < unat len"
    using i_lt k_lt by (rule unat_less_suc_word_le_len)
  have i_len: "unat i < unat len"
    using i_lt by (simp add: word_less_nat_alt)
  have ptr_ne0:
    "buf +\<^sub>p uint (pos + of_nat k) \<noteq>
     buf +\<^sub>p uint (pos + of_nat (unat i))"
    using dst_inj[rule_format, of k "unat i"] k_ne k_len i_len
    by simp
  have ptr_ne:
    "buf +\<^sub>p uint (pos + of_nat k) \<noteq>
     buf +\<^sub>p uint (pos + i)"
    using ptr_ne0
    by (simp add: word_unat.Rep_inverse)
  show False
    using ptr_ne ptr_eq by simp
qed

lemma word_index_ptr_ne_currentD:
  fixes len pos i :: "32 word"
  assumes i_lt: "i < len"
      and k_lt: "k < unat (i + 1)"
      and ptr_ne:
        "buf +\<^sub>p uint (pos + of_nat k) \<noteq>
         buf +\<^sub>p uint (pos + i)"
  shows "k < unat i"
proof (cases "k = unat i")
  case True
  have "buf +\<^sub>p uint (pos + of_nat k) =
        buf +\<^sub>p uint (pos + i)"
    using True by (simp add: word_unat.Rep_inverse)
  thus ?thesis
    using ptr_ne by simp
next
  case False
  show ?thesis
    using i_lt k_lt False by (rule unat_less_suc_word_prevD)
qed

lemma dst_src_disj_current_contradict:
  fixes len pos src_off i :: "32 word"
  assumes dst_src_disj: "\<forall>a < unat len. \<forall>b < unat len.
           buf +\<^sub>p uint (pos + of_nat a) \<noteq>
           src +\<^sub>p uint (src_off + of_nat b)"
      and i_lt: "i < len"
      and k_lt: "k < unat len"
      and ptr_eq:
        "src +\<^sub>p uint (src_off + of_nat k) =
         buf +\<^sub>p uint (pos + i)"
  shows False
proof -
  have i_len: "unat i < unat len"
    using i_lt by (simp add: word_less_nat_alt)
  have ptr_ne0:
    "buf +\<^sub>p uint (pos + of_nat (unat i)) \<noteq>
     src +\<^sub>p uint (src_off + of_nat k)"
    using dst_src_disj[rule_format, of "unat i" k] i_len k_lt
    by simp
  have ptr_ne:
    "buf +\<^sub>p uint (pos + i) \<noteq>
     src +\<^sub>p uint (src_off + of_nat k)"
    using ptr_ne0
    by (simp add: word_unat.Rep_inverse)
  show False
    using ptr_ne ptr_eq by simp
qed

lemma write_byte'_spec:
  assumes ptr_ok:
    "pos < cap \<Longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. if cap \<le> pos
                   then t = s \<and> r = Result (wr_t_C pos ENC_OVERFLOW)
                   else t = heap_w8_update (\<lambda>h. h(buf +\<^sub>p uint pos := b)) s \<and>
                        r = Result (wr_t_C (pos + 1) ENC_OK) \<rbrace>"
  unfolding write_byte'_def
  apply runs_to_vcg
  using ptr_ok by auto

lemma write_bytes'_overflow:
  assumes overflow: "cap - pos < len"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and> r = Result (wr_t_C pos ENC_OVERFLOW) \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  using overflow by simp

lemma write_bytes'_zero:
  shows "write_bytes' buf cap pos src src_off 0 \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and> r = Result (wr_t_C pos ENC_OK) \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat (0 :: 32 word) - unat i)"
      and I = "\<lambda>i t. i = 0 \<and> t = s"])
     apply simp
    apply simp
   apply simp
  apply runs_to_vcg
  done

lemma write_bytes_loop_preserves_typing:
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
         \<lbrace> \<lambda>r t. r = Result len \<and> heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len \<and>
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

lemma write_bytes_loop_copies:
  fixes len pos src_off :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
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
            (\<forall>j < unat len.
              heap_w8 t (src +\<^sub>p uint (src_off + of_nat j)) =
              heap_w8 s (src +\<^sub>p uint (src_off + of_nat j))) \<and>
            (\<forall>j < unat len.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              heap_w8 s (src +\<^sub>p uint (src_off + of_nat j))) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len
             \<and> (\<forall>k < unat len.
                 heap_w8 st (src +\<^sub>p uint (src_off + of_nat k)) =
                 heap_w8 s (src +\<^sub>p uint (src_off + of_nat k)))
             \<and> (\<forall>k < unat i.
                 heap_w8 st (buf +\<^sub>p uint (pos + of_nat k)) =
                 heap_w8 s (src +\<^sub>p uint (src_off + of_nat k)))
             \<and> heap_typing st = heap_typing s"])
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
    apply (auto simp: runs_to.rep_eq run_bind run_guard run_modify fun_upd_apply
                      word_less_nat_alt word_unat.Rep_inverse
                intro: unat_suc_le_of_word_less
                       unat_measure_decrease_of_word_less)
    subgoal premises prems for k
    proof -
      have i_word: "i < len"
        using prems(1) by (simp add: word_less_nat_alt)
      have contradiction: False
        by (rule dst_src_disj_current_contradict
          [OF dst_src_disj i_word prems(8) prems(7)])
      show ?thesis
        using contradiction by simp
    qed
    subgoal premises prems for k
    proof -
      have i_word: "i < len"
        using prems(1) by (simp add: word_less_nat_alt)
      have k_eq: "k = unat i"
        by (rule word_index_ptr_eq_currentD
          [OF dst_inj i_word prems(8) prems(7)])
      have src_pres:
        "heap_w8 st (src +\<^sub>p uint (src_off + i)) =
         heap_w8 s (src +\<^sub>p uint (src_off + i))"
        using prems(4)[rule_format, of "unat i"] prems(1)
        by (simp add: word_unat.Rep_inverse)
      show ?thesis
        using k_eq src_pres by simp
    qed
    subgoal premises prems for k
    proof -
      have i_word: "i < len"
        using prems(1) by (simp add: word_less_nat_alt)
      have k_prev: "k < unat i"
        by (rule word_index_ptr_ne_currentD
          [OF i_word prems(8) prems(7)])
      show ?thesis
        using prems(5)[rule_format, OF k_prev] by simp
    qed
    done
  done

lemma write_bytes'_success_preserves_typing:
  assumes fits: "\<not> cap - pos < len"
      and dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  using fits
  apply simp
  apply (rule runs_to_weaken[
    OF write_bytes_loop_preserves_typing[OF dst_valid src_valid]])
  by auto

lemma write_bytes'_success_copies:
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
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
            (\<forall>j < unat len.
              heap_w8 t (src +\<^sub>p uint (src_off + of_nat j)) =
              heap_w8 s (src +\<^sub>p uint (src_off + of_nat j))) \<and>
            (\<forall>j < unat len.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              heap_w8 s (src +\<^sub>p uint (src_off + of_nat j))) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  using fits
  apply simp
  apply (rule runs_to_weaken[
    OF write_bytes_loop_copies
      [OF dst_valid src_valid dst_src_disj dst_inj]])
  by auto

lemma write_varint'_overflow:
  assumes size: "varint_size' v s = Some n"
      and overflow: "cap - pos < n"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and> r = Result (wr_t_C pos ENC_OVERFLOW) \<rbrace>"
  unfolding write_varint'_def
  apply runs_to_vcg
  using size overflow by auto

lemma gets_the_varint_size'_result:
  assumes "varint_size' v s = Some n"
  shows "gets_the (varint_size' v) \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and> r = Result n \<rbrace>"
  unfolding gets_the_def
  apply runs_to_vcg
  using assms by simp

lemma write_varint'_overflow_preserves_typing:
  assumes size: "varint_size' v s = Some n"
      and overflow: "cap - pos < n"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and>
                   r = Result (wr_t_C pos ENC_OVERFLOW) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[OF write_varint'_overflow[OF size overflow]])
  by auto

definition varint_byte32 :: "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 8 word" where
  "varint_byte32 v len i =
     (let b = (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F) :: 8 word) in
      if i + 1 < len
      then (ucast ((ucast b :: 32 word) || 0x80) :: 8 word)
      else b)"

definition varint_digit32 :: "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> nat" where
  "varint_digit32 v len i =
     unat ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F :: 32 word)"

definition varint_digits32 :: "32 word \<Rightarrow> 32 word \<Rightarrow> nat list" where
  "varint_digits32 v len =
     map (\<lambda>i. varint_digit32 v len (of_nat i)) [0 ..< unat len]"

definition varint_bytes32 :: "32 word \<Rightarrow> 32 word \<Rightarrow> byte list" where
  "varint_bytes32 v len =
     map (\<lambda>i. varint_byte32 v len (of_nat i)) [0 ..< unat len]"

lemma varint_digit32_bound[simp]:
  "varint_digit32 v len i < 128"
proof -
  have "((v >> unat (7 * len - 7 - 7 * i)) && 0x7F :: 32 word) \<le> 0x7F"
    by (simp add: word_and_le1)
  hence "unat ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F :: 32 word) \<le> 127"
    by (simp add: word_le_nat_alt)
  thus ?thesis
    by (simp add: varint_digit32_def)
qed

lemma varint_digits32_length[simp]:
  "length (varint_digits32 v len) = unat len"
  by (simp add: varint_digits32_def)

lemma varint_digits32_bound:
  "\<forall>d \<in> set (varint_digits32 v len). d < 128"
  by (simp add: varint_digits32_def)

lemma byte_ucast32_or_80:
  fixes b :: byte
  shows "(ucast ((ucast b :: 32 word) || 0x80) :: byte) = b OR 0x80"
  by (intro word_eqI) (auto simp: bit_simps word_size)

lemma varint_byte32_digit:
  "varint_byte32 v len i =
     (let d = (word_of_nat (varint_digit32 v len i) :: byte) in
      if i + 1 < len then d OR 0x80 else d)"
  unfolding varint_byte32_def varint_digit32_def
  by (simp add: Let_def word_unat.Rep_inverse byte_ucast32_or_80)

lemma set_cont_bits_map_nth:
  assumes i_lt: "i < length ds"
  shows "set_cont_bits (map (\<lambda>d. word_of_nat d :: byte) ds) ! i =
         (if Suc i < length ds
          then (word_of_nat (ds ! i) :: byte) OR 0x80
          else word_of_nat (ds ! i))"
  using i_lt
proof (induction ds arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  show ?case
  proof (cases i)
    case 0
    show ?thesis
      using 0 by (cases ds) simp_all
  next
    case (Suc i')
    have i'_lt: "i' < length ds"
      using Cons.prems Suc by simp
    show ?thesis
      using Cons.IH[OF i'_lt] Suc Cons.prems
      by (cases ds) simp_all
  qed
qed

lemma varint_bytes32_eq_set_cont_bits:
  assumes len_le: "unat len \<le> 5"
  shows "varint_bytes32 v len =
         set_cont_bits (map (\<lambda>d. word_of_nat d :: byte)
           (varint_digits32 v len))"
proof (rule nth_equalityI)
  show "length (varint_bytes32 v len) =
        length (set_cont_bits (map (\<lambda>d. word_of_nat d :: byte)
          (varint_digits32 v len)))"
    by (simp add: varint_bytes32_def)
next
  fix i
  assume i_lt_len:
    "i < length (varint_bytes32 v len)"
  hence i_lt: "i < unat len"
    by (simp add: varint_bytes32_def)
  have i_word_lt32: "i < 2 ^ 32"
    using i_lt unat_lt2p[of len] by simp
  have suc_unat:
    "unat ((of_nat i :: 32 word) + 1) = Suc i"
    using i_lt len_le
    by (simp add: Word.unat_arith_simps unat_of_nat_eq)
  have branch:
    "((of_nat i :: 32 word) + 1 < len) \<longleftrightarrow> Suc i < unat len"
    using suc_unat by (simp add: word_less_nat_alt)
  have digit_nth:
    "varint_digits32 v len ! i = varint_digit32 v len (of_nat i)"
    using i_lt by (simp add: varint_digits32_def)
  show "varint_bytes32 v len ! i =
        set_cont_bits (map (\<lambda>d. word_of_nat d :: byte)
          (varint_digits32 v len)) ! i"
    using i_lt digit_nth branch
    by (simp add: varint_bytes32_def varint_byte32_digit
                  set_cont_bits_map_nth)
qed

lemma varint_decode_varint_bytes32_digits:
  assumes len_pos: "0 < unat len"
      and len_le: "unat len \<le> 5"
      and value_bound: "from_base128_acc 0 (varint_digits32 v len) < 2 ^ 32"
  shows "varint_decode (varint_bytes32 v len @ rest) =
         Some (from_base128_acc 0 (varint_digits32 v len), rest)"
proof -
  have digits_nonempty: "varint_digits32 v len \<noteq> []"
    using len_pos by (simp add: varint_digits32_def)
  have digits_bound: "\<forall>d \<in> set (varint_digits32 v len). d < 128"
    by (rule varint_digits32_bound)
  have digits_len: "length (varint_digits32 v len) \<le> 5"
    using len_le by simp
  show ?thesis
    using varint_decode_loop_on_encoded
      [OF digits_nonempty digits_bound digits_len value_bound, of rest]
          varint_bytes32_eq_set_cont_bits[OF len_le, of v]
    by (simp add: varint_decode_def)
qed

lemma base128_mod_split:
  fixes x n :: nat
  shows "((x div 128 ^ n) mod 128) * 128 ^ n + x mod 128 ^ n =
         x mod 128 ^ Suc n"
  using mod_mult2_eq[of x "128 ^ n" 128]
  by (simp add: ac_simps)

lemma from_base128_acc_fixed_digits:
  "from_base128_acc acc
     (map (\<lambda>i. (x div 128 ^ (len - Suc i)) mod 128) [0 ..< len]) =
   acc * 128 ^ len + x mod 128 ^ len"
proof (induction len arbitrary: acc)
  case 0
  show ?case by simp
next
  case (Suc len)
  have split:
    "x mod 128 ^ len + 128 ^ len * (x div 128 ^ len mod 128) =
     x mod (128 * 128 ^ len)"
    using base128_mod_split[of x len] by (simp add: ac_simps)
  show ?case
    by (simp add: map_upt_Suc Suc.IH split algebra_simps del: upt_Suc)
qed

lemma unat_and_0x7F_mod32:
  fixes w :: "32 word"
  shows "unat (w AND 0x7F) = unat w mod 128"
  apply transfer
  subgoal for w
  proof -
    have and_eq: "w AND 127 = w mod 128"
    proof -
      have mask_eq: "(127 :: int) = mask 7"
        by (simp add: mask_eq_exp_minus_1)
      have "w AND 127 = w AND mask 7"
        by (simp add: mask_eq)
      also have "\<dots> = take_bit 7 w"
        by (simp add: take_bit_eq_mask)
      also have "\<dots> = w mod 128"
        by (simp add: take_bit_eq_mod)
      finally show ?thesis .
    qed
    have mod_eq: "(w mod 4294967296) mod 128 = w mod 128"
      by (simp add: mod_mod_cancel)
    have nat_mod:
      "nat (w mod 4294967296) mod 128 =
       nat ((w mod 4294967296) mod 128)"
      using nat_mod_distrib[of "w mod 4294967296" 128] by simp
    have low32: "(w mod 128) mod 4294967296 = w mod 128"
      by (simp add: mod_pos_pos_trivial)
    show ?thesis
      using and_eq mod_eq nat_mod low32
      by (simp add: take_bit_eq_mod)
  qed
  done

lemma varint_shift_unat_nat_index:
  fixes len :: "32 word"
  assumes len_le: "unat len \<le> 5"
      and i_lt: "i < unat len"
  shows "unat (7 * len - 7 - 7 * (of_nat i :: 32 word)) =
         7 * (unat len - Suc i)"
proof -
  have i_unat: "unat (of_nat i :: 32 word) = i"
    using i_lt unat_lt2p[of len] by (simp add: unat_of_nat_eq)
  have i_word_lt: "unat (of_nat i :: 32 word) < unat len"
    using i_lt i_unat by simp
  have len_mult: "unat (7 * len :: 32 word) = 7 * unat len"
    using len_le by (simp add: Word.unat_word_ariths)
  have i_mult:
    "unat (7 * (of_nat i :: 32 word) :: 32 word) = 7 * i"
    using len_le i_lt by (simp add: Word.unat_word_ariths i_unat)
  have arith_eq:
    "7 * unat len - (7 + 7 * i) = 7 * (unat len - Suc i)"
    using i_lt by arith
  show ?thesis
    using len_le i_lt i_word_lt len_mult i_mult arith_eq
    by (simp add: Word.unat_arith_simps i_unat)
qed

lemma varint_digit32_eq_div_mod:
  assumes len_le: "unat len \<le> 5"
      and i_lt: "i < unat len"
  shows "varint_digit32 v len (of_nat i) =
         (unat v div 128 ^ (unat len - Suc i)) mod 128"
proof -
  have shift:
    "unat (7 * len - 7 - 7 * (of_nat i :: 32 word)) =
     7 * (unat len - Suc i)"
    by (rule varint_shift_unat_nat_index[OF len_le i_lt])
  show ?thesis
    unfolding varint_digit32_def
    by (simp add: shift unat_and_0x7F_mod32
                  Word_Lemmas.shiftr_div_2n' power_mult)
qed

lemma varint_digits32_value_mod:
  assumes len_le: "unat len \<le> 5"
  shows "from_base128_acc acc (varint_digits32 v len) =
         acc * 128 ^ unat len + unat v mod 128 ^ unat len"
proof -
  have digits_eq:
    "varint_digits32 v len =
     map (\<lambda>i. (unat v div 128 ^ (unat len - Suc i)) mod 128)
       [0 ..< unat len]"
    unfolding varint_digits32_def
  proof (rule map_cong[OF refl])
    fix i
    assume "i \<in> set [0 ..< unat len]"
    hence i_lt: "i < unat len"
      by simp
    show "varint_digit32 v len (of_nat i) =
          (unat v div 128 ^ (unat len - Suc i)) mod 128"
      by (rule varint_digit32_eq_div_mod[OF len_le i_lt])
  qed
  show ?thesis
    by (simp add: digits_eq from_base128_acc_fixed_digits)
qed

lemma shiftr_zero_unat_lt_power:
  fixes v :: "32 word"
  assumes "v >> k = 0"
  shows "unat v < 2 ^ k"
proof -
  have "unat (v >> k) = unat v div 2 ^ k"
    by (simp add: Word_Lemmas.shiftr_div_2n')
  hence "unat v div 2 ^ k = 0"
    using assms by simp
  thus ?thesis
    by (simp add: div_eq_0_iff)
qed

lemma varint_digits32_value:
  assumes size: "varint_size' v s = Some n"
  shows "from_base128_acc 0 (varint_digits32 v n) = unat v"
proof -
  have n_le: "unat n \<le> 5"
    by (rule varint_size'_le5[OF size])
  have folded:
    "from_base128_acc 0 (varint_digits32 v n) =
     unat v mod 128 ^ unat n"
    using varint_digits32_value_mod[OF n_le, of 0 v] by simp
  have shift0: "v >> (7 * unat n) = 0"
    by (rule varint_size'_shiftr_zero[OF size])
  have pow_eq: "(2 :: nat) ^ (7 * unat n) = 128 ^ unat n"
    by (simp add: power_mult)
  have v_lt: "unat v < 128 ^ unat n"
    using shiftr_zero_unat_lt_power[OF shift0] pow_eq by simp
  show ?thesis
    using folded v_lt by simp
qed

lemma varint_decode_varint_bytes32:
  assumes size: "varint_size' v s = Some n"
  shows "varint_decode (varint_bytes32 v n @ rest) =
         Some (unat v, rest)"
proof -
  have n_pos: "0 < unat n"
    using varint_size'_ge1[OF size] by simp
  have n_le: "unat n \<le> 5"
    by (rule varint_size'_le5[OF size])
  have decoded_value: "from_base128_acc 0 (varint_digits32 v n) = unat v"
    by (rule varint_digits32_value[OF size])
  have value_bound: "from_base128_acc 0 (varint_digits32 v n) < 2 ^ 32"
    using decoded_value unat_lt2p[of v] by simp
  show ?thesis
    using varint_decode_varint_bytes32_digits[OF n_pos n_le value_bound]
          decoded_value
    by simp
qed

lemma write_varint_loop_preserves_typing:
  fixes len pos :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < len \<longrightarrow>
           7 * len - 7 - 7 * i < (0x20 :: 32 word)"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. i < len)
           (\<lambda>i. do {
              guard (\<lambda>st. 7 * len - 7 - 7 * i < (0x20 :: 32 word));
              guard (\<lambda>st. ptr_valid (heap_typing st) (buf +\<^sub>p uint (pos + i)));
              modify (heap_w8_update
                (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                  if i + 1 < len
                  then (ucast
                    ((ucast
                      (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word) :: 32 word) || 0x80) :: 8 word)
                  else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word))));
              return (i + 1)
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result len \<and> heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len \<and>
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
          shift_ok[rule_format, of i]
    by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                   word_less_nat_alt word_unat.Rep_inverse
             intro: unat_suc_le_of_word_less
                    unat_measure_decrease_of_word_less)
  done

lemma write_varint_loop_writes:
  fixes len pos :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < len \<longrightarrow>
           7 * len - 7 - 7 * i < (0x20 :: 32 word)"
      and dst_inj: "\<forall>i < unat len. \<forall>j < unat len.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. i < len)
           (\<lambda>i. do {
              guard (\<lambda>st. 7 * len - 7 - 7 * i < (0x20 :: 32 word));
              guard (\<lambda>st. ptr_valid (heap_typing st) (buf +\<^sub>p uint (pos + i)));
              modify (heap_w8_update
                (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                  if i + 1 < len
                  then (ucast
                    ((ucast
                      (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word) :: 32 word) || 0x80) :: 8 word)
                  else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word))));
              return (i + 1)
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result len \<and>
            (\<forall>j < unat len.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              varint_byte32 v len (of_nat j)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len
             \<and> (\<forall>k < unat i.
                 heap_w8 st (buf +\<^sub>p uint (pos + of_nat k)) =
                 varint_byte32 v len (of_nat k))
             \<and> heap_typing st = heap_typing s"])
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
          shift_ok[rule_format, of i]
    apply (auto simp: runs_to.rep_eq run_bind run_guard run_modify fun_upd_apply
                      word_less_nat_alt word_unat.Rep_inverse varint_byte32_def
                intro: unat_suc_le_of_word_less
                       unat_measure_decrease_of_word_less)
    subgoal premises prems for k
    proof -
      have i_word: "i < len"
        using prems(1) by (simp add: word_less_nat_alt)
      have k_lt: "k < unat (i + 1)"
        using prems by simp
      have ptr_eq:
        "buf +\<^sub>p uint (pos + of_nat k) =
         buf +\<^sub>p uint (pos + i)"
        using prems by simp
      have k_eq: "k = unat i"
        by (rule word_index_ptr_eq_currentD
          [OF dst_inj i_word k_lt ptr_eq])
      have cont: "unat (i + 1) < unat len"
        using prems by (simp add: word_less_nat_alt)
      show ?thesis
        using k_eq cont
        by (simp add: word_unat.Rep_inverse varint_byte32_def)
    qed
    subgoal premises prems for k
    proof -
      have i_word: "i < len"
        using prems(1) by (simp add: word_less_nat_alt)
      have k_lt: "k < unat (i + 1)"
        using prems by simp
      have ptr_ne:
        "buf +\<^sub>p uint (pos + of_nat k) \<noteq>
         buf +\<^sub>p uint (pos + i)"
        using prems by simp
      have k_prev: "k < unat i"
        by (rule word_index_ptr_ne_currentD
          [OF i_word k_lt ptr_ne])
      show ?thesis
        using prems k_prev by simp
    qed
    subgoal premises prems
    proof -
      have i_word: "i < len"
        using prems(1) by (simp add: word_less_nat_alt)
      have suc_le: "unat (i + 1) \<le> unat len"
        using i_word by (rule unat_suc_le_of_word_less)
      have len_le: "unat len \<le> unat (i + 1)"
        using prems by simp
      have "unat (i + 1) = unat len"
        using suc_le len_le by simp
      thus ?thesis
        by (metis word_unat.Rep_inject)
    qed
    subgoal premises prems for k
    proof -
      have i_word: "i < len"
        using prems(1) by (simp add: word_less_nat_alt)
      have k_lt: "k < unat (i + 1)"
        using prems by simp
      have ptr_eq:
        "buf +\<^sub>p uint (pos + of_nat k) =
         buf +\<^sub>p uint (pos + i)"
        using prems by simp
      have k_eq: "k = unat i"
        by (rule word_index_ptr_eq_currentD
          [OF dst_inj i_word k_lt ptr_eq])
      have final: "\<not> unat (i + 1) < unat len"
        using prems by simp
      show ?thesis
        using k_eq final
        by (simp add: word_unat.Rep_inverse varint_byte32_def)
    qed
    subgoal premises prems for k
    proof -
      have i_word: "i < len"
        using prems(1) by (simp add: word_less_nat_alt)
      have k_lt: "k < unat (i + 1)"
        using prems by simp
      have ptr_ne:
        "buf +\<^sub>p uint (pos + of_nat k) \<noteq>
         buf +\<^sub>p uint (pos + i)"
        using prems by simp
      have k_prev: "k < unat i"
        by (rule word_index_ptr_ne_currentD
          [OF i_word k_lt ptr_ne])
      show ?thesis
        using prems k_prev by simp
    qed
    done
  done

lemma write_varint'_success_preserves_typing:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_varint'_def
  apply runs_to_vcg
  using size fits
  apply simp
  apply runs_to_vcg
  apply (rule runs_to_weaken[
    OF write_varint_loop_preserves_typing[OF dst_valid shift_ok]])
  by auto

lemma write_varint'_success_preserves_typing_le5:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and n_le: "unat n \<le> 5"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_preserves_typing[OF size fits dst_valid])
  using n_le by (auto intro: varint_shift_ok_of_unat_le5)

lemma write_varint'_success_preserves_typing_bounded:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_preserves_typing_le5
    [OF size fits dst_valid])
  using varint_size'_le5[OF size] .

lemma write_varint'_success_writes:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            (\<forall>j < unat n.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              varint_byte32 v n (of_nat j)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  unfolding write_varint'_def
  apply runs_to_vcg
  using size fits
  apply simp
  apply runs_to_vcg
  apply (rule runs_to_weaken[
    OF write_varint_loop_writes[OF dst_valid shift_ok dst_inj]])
  by auto

lemma write_varint'_success_writes_le5:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and n_le: "unat n \<le> 5"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            (\<forall>j < unat n.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              varint_byte32 v n (of_nat j)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_writes[OF size fits dst_valid _ dst_inj])
  using n_le by (auto intro: varint_shift_ok_of_unat_le5)

lemma write_varint'_success_writes_bounded:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            (\<forall>j < unat n.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              varint_byte32 v n (of_nat j)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_writes_le5
    [OF size fits dst_valid _ dst_inj])
  using varint_size'_le5[OF size] .

(* ---------- Buffer-to-list conversion ---------- *)

definition heap_bytes :: "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> byte list" where
  "heap_bytes s buf n = map (\<lambda>i. heap_w8 s (buf +\<^sub>p int i)) [0 ..< n]"

definition heap_bytes_word :: "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> byte list" where
  "heap_bytes_word s buf pos len =
     map (\<lambda>i. heap_w8 s (buf +\<^sub>p uint (pos + of_nat i))) [0 ..< unat len]"

definition emitted_sections ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow>
   sections_t_C \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> bool" where
  "emitted_sections st data inst addr r data_bytes inst_bytes addr_bytes \<longleftrightarrow>
     heap_bytes st data (unat (sections_t_C.data_pos_C r)) = data_bytes \<and>
     heap_bytes st inst (unat (sections_t_C.inst_pos_C r)) = inst_bytes \<and>
     heap_bytes st addr (unat (sections_t_C.addr_pos_C r)) = addr_bytes"

lemma emitted_sectionsD:
  assumes "emitted_sections st data inst addr r data_bytes inst_bytes addr_bytes"
  shows "heap_bytes st data (unat (sections_t_C.data_pos_C r)) = data_bytes"
        "heap_bytes st inst (unat (sections_t_C.inst_pos_C r)) = inst_bytes"
        "heap_bytes st addr (unat (sections_t_C.addr_pos_C r)) = addr_bytes"
  using assms by (simp_all add: emitted_sections_def)

lemma heap_bytes_length[simp]:
  "length (heap_bytes s buf n) = n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_word_length[simp]:
  "length (heap_bytes_word s buf pos len) = unat len"
  by (simp add: heap_bytes_word_def)

lemma heap_bytes_nth:
  "i < n \<Longrightarrow> heap_bytes s buf n ! i = heap_w8 s (buf +\<^sub>p int i)"
  by (simp add: heap_bytes_def)

lemma heap_bytes_word_nth:
  "i < unat len \<Longrightarrow>
   heap_bytes_word s buf pos len ! i =
   heap_w8 s (buf +\<^sub>p uint (pos + of_nat i))"
  by (simp add: heap_bytes_word_def)

lemma heap_bytes_word_zero:
  fixes len :: "32 word"
  shows "heap_bytes_word s buf 0 len = heap_bytes s buf (unat len)"
proof (rule nth_equalityI)
  show "length (heap_bytes_word s buf 0 len) =
        length (heap_bytes s buf (unat len))"
    by simp
next
  fix i
  assume i_lt_len: "i < length (heap_bytes_word s buf 0 len)"
  hence i_lt: "i < unat len"
    by simp
  have i_lt32: "i < 2 ^ 32"
    using i_lt unat_lt2p[of len] by simp
  have i_unat: "unat (of_nat i :: 32 word) = i"
    using i_lt32 by (simp add: unat_of_nat_eq)
  show "heap_bytes_word s buf 0 len ! i =
        heap_bytes s buf (unat len) ! i"
    using i_lt i_unat by (simp add: heap_bytes_word_nth heap_bytes_nth uint_nat)
qed

lemma heap_bytes_eqI:
  assumes "\<And>i. i < n \<Longrightarrow> heap_w8 t (buf +\<^sub>p int i) = heap_w8 s (buf +\<^sub>p int i)"
  shows "heap_bytes t buf n = heap_bytes s buf n"
  using assms by (auto simp: heap_bytes_def)

lemma heap_bytes_word_eqI:
  assumes "\<And>i. i < unat len \<Longrightarrow>
           heap_w8 t (buf +\<^sub>p uint (pos + of_nat i)) =
           heap_w8 s (buf +\<^sub>p uint (pos + of_nat i))"
  shows "heap_bytes_word t buf pos len = heap_bytes_word s buf pos len"
  using assms by (auto simp: heap_bytes_word_def)

lemma write_byte'_success_heap_bytes_word_single:
  assumes fits: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes_word t buf pos 1 = [b] \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[OF write_byte'_spec])
  subgoal
    using ptr_ok .
  subgoal
    using fits by (auto simp: heap_bytes_word_def)
  done

lemma write_varint'_overflow_preserves_heap_bytes:
  assumes size: "varint_size' v s = Some n"
      and overflow: "cap - pos < n"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C pos ENC_OVERFLOW) \<and>
                   heap_bytes t out out_n = heap_bytes s out out_n \<rbrace>"
  apply (rule runs_to_weaken[OF write_varint'_overflow[OF size overflow]])
  by auto

lemma write_varint'_success_writes_heap_bytes_word:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes_word t buf pos n = varint_bytes32 v n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_varint'_success_writes_bounded
      [OF size fits dst_valid dst_inj]])
  by (auto simp: heap_bytes_word_def varint_bytes32_def)

lemma heap_bytes_word_varint_decode:
  assumes size: "varint_size' v s = Some n"
      and bytes: "heap_bytes_word t buf pos n = varint_bytes32 v n"
  shows "varint_decode (heap_bytes_word t buf pos n @ rest) =
         Some (unat v, rest)"
  using bytes varint_decode_varint_bytes32[OF size, of rest] by simp

lemma write_varint'_success_decodes_heap_bytes_word:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes_word t buf pos n = varint_bytes32 v n \<and>
                   varint_decode (heap_bytes_word t buf pos n @ rest) =
                     Some (unat v, rest) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_varint'_success_writes_heap_bytes_word
      [OF size fits dst_valid dst_inj]])
  using heap_bytes_word_varint_decode[OF size, of _ buf pos rest]
  by auto

lemma write_bytes'_success_copies_heap_bytes_word:
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
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes_word t buf pos len =
                   heap_bytes_word s src src_off len \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_bytes'_success_copies
      [OF fits dst_valid src_valid dst_src_disj dst_inj]])
  by (auto simp: heap_bytes_word_def)

lemma heap_bytes_prefix:
  assumes "m \<le> n"
  shows "take m (heap_bytes s buf n) = heap_bytes s buf m"
proof (rule nth_equalityI)
  show "length (take m (heap_bytes s buf n)) = length (heap_bytes s buf m)"
    using assms by simp
next
  fix i
  assume i_lt: "i < length (take m (heap_bytes s buf n))"
  hence i_m: "i < m" using assms by simp
  hence i_n: "i < n" using assms by simp
  show "take m (heap_bytes s buf n) ! i = heap_bytes s buf m ! i"
    using i_m i_n by (simp add: heap_bytes_nth)
qed

lemma heap_bytes_slice:
  assumes "off + n \<le> len"
  shows "take n (drop off (heap_bytes s buf len)) =
         heap_bytes s (buf +\<^sub>p int off) n"
proof (rule nth_equalityI)
  show "length (take n (drop off (heap_bytes s buf len))) =
        length (heap_bytes s (buf +\<^sub>p int off) n)"
    using assms by simp
next
  fix i
  assume "i < length (take n (drop off (heap_bytes s buf len)))"
  hence i_lt: "i < n" and off_i_lt: "off + i < len"
    using assms by auto
  have ptr_eq: "buf +\<^sub>p int (off + i) = buf +\<^sub>p int off +\<^sub>p int i"
    by (simp add: ptr_add_def)
  show "take n (drop off (heap_bytes s buf len)) ! i =
        heap_bytes s (buf +\<^sub>p int off) n ! i"
    using i_lt off_i_lt ptr_eq
    by (simp add: heap_bytes_nth)
qed

lemma heap_bytes_append_heap_bytes_word:
  assumes no_overflow: "unat pos + unat len < 2 ^ 32"
  shows "heap_bytes s buf (unat pos + unat len) =
         heap_bytes s buf (unat pos) @ heap_bytes_word s buf pos len"
proof (rule nth_equalityI)
  show "length (heap_bytes s buf (unat pos + unat len)) =
        length (heap_bytes s buf (unat pos) @ heap_bytes_word s buf pos len)"
    by simp
next
  fix i
  assume i_lt_len:
    "i < length (heap_bytes s buf (unat pos + unat len))"
  hence i_lt: "i < unat pos + unat len"
    by simp
  show "heap_bytes s buf (unat pos + unat len) ! i =
        (heap_bytes s buf (unat pos) @ heap_bytes_word s buf pos len) ! i"
  proof (cases "i < unat pos")
    case True
    show ?thesis
      using True i_lt
      by (simp add: heap_bytes_nth nth_append)
  next
    case False
    let ?j = "i - unat pos"
    have j_lt: "?j < unat len"
      using False i_lt by simp
    have i_eq: "i = unat pos + ?j"
      using False by simp
    have idx:
      "unat (pos + of_nat ?j :: 32 word) = unat pos + ?j"
      by (rule unat_add_of_nat_index[OF j_lt no_overflow])
    show ?thesis
      using False j_lt i_eq idx
      by (simp add: heap_bytes_nth heap_bytes_word_nth nth_append uint_nat)
  qed
qed

lemma heap_bytes_take_word_prefix:
  fixes pos len :: "32 word"
  assumes no_overflow: "unat pos + unat len < 2 ^ 32"
  shows "take (unat pos) (heap_bytes s buf (unat pos + unat len)) =
         heap_bytes s buf (unat pos)"
  using heap_bytes_append_heap_bytes_word[OF no_overflow, of s buf]
  by simp

lemma heap_bytes_drop_word_prefix:
  fixes pos len :: "32 word"
  assumes no_overflow: "unat pos + unat len < 2 ^ 32"
  shows "drop (unat pos) (heap_bytes s buf (unat pos + unat len)) =
         heap_bytes_word s buf pos len"
  using heap_bytes_append_heap_bytes_word[OF no_overflow, of s buf]
  by simp

(* ---------- Buffer validity ---------- *)

definition buf_valid :: "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "buf_valid s buf n =
     (\<forall>i < n. ptr_valid (heap_typing s) (buf +\<^sub>p int i))"

lemma buf_validD:
  "\<lbrakk> buf_valid s buf n; i < n \<rbrakk> \<Longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p int i)"
  by (simp add: buf_valid_def)

lemma buf_valid_mono:
  "\<lbrakk> buf_valid s buf n; m \<le> n \<rbrakk> \<Longrightarrow> buf_valid s buf m"
  by (auto simp: buf_valid_def)

lemma buf_valid_uintD:
  assumes ok: "buf_valid s buf n"
      and i_lt: "unat i < n"
  shows "ptr_valid (heap_typing s) (buf +\<^sub>p uint i)"
proof -
  have "ptr_valid (heap_typing s) (buf +\<^sub>p int (unat i))"
    using buf_validD[OF ok i_lt] .
  thus ?thesis by (simp only: uint_nat)
qed

lemma buf_valid_word_rangeD:
  fixes base len :: "32 word"
  assumes ok: "buf_valid s buf n"
      and j_lt: "j < unat len"
      and no_overflow: "unat base + unat len < 2 ^ 32"
      and in_range: "unat base + unat len \<le> n"
  shows "ptr_valid (heap_typing s) (buf +\<^sub>p uint (base + of_nat j :: 32 word))"
proof -
  have idx: "unat (base + of_nat j :: 32 word) = unat base + j"
    by (rule unat_add_of_nat_index[OF j_lt no_overflow])
  have "unat (base + of_nat j :: 32 word) < n"
    using j_lt in_range idx by simp
  thus ?thesis
    by (rule buf_valid_uintD[OF ok])
qed

lemma write_bytes'_success_preserves_typing_buf_valid:
  assumes fits: "\<not> cap - pos < len"
      and dst_ok: "buf_valid s buf dst_n"
      and src_ok: "buf_valid s src src_n"
      and dst_no_overflow: "unat pos + unat len < 2 ^ 32"
      and src_no_overflow: "unat src_off + unat len < 2 ^ 32"
      and dst_range: "unat pos + unat len \<le> dst_n"
      and src_range: "unat src_off + unat len \<le> src_n"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_bytes'_success_preserves_typing[OF fits])
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  done

lemma write_bytes'_success_copies_buf_valid:
  assumes fits: "\<not> cap - pos < len"
      and dst_ok: "buf_valid s buf dst_n"
      and src_ok: "buf_valid s src src_n"
      and dst_no_overflow: "unat pos + unat len < 2 ^ 32"
      and src_no_overflow: "unat src_off + unat len < 2 ^ 32"
      and dst_range: "unat pos + unat len \<le> dst_n"
      and src_range: "unat src_off + unat len \<le> src_n"
      and dst_src_disj: "\<forall>i < unat len. \<forall>j < unat len.
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           src +\<^sub>p uint (src_off + of_nat j)"
      and dst_inj: "\<forall>i < unat len. \<forall>j < unat len.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
            (\<forall>j < unat len.
              heap_w8 t (src +\<^sub>p uint (src_off + of_nat j)) =
              heap_w8 s (src +\<^sub>p uint (src_off + of_nat j))) \<and>
            (\<forall>j < unat len.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              heap_w8 s (src +\<^sub>p uint (src_off + of_nat j))) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_bytes'_success_copies[OF fits])
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  subgoal
    using dst_src_disj .
  subgoal
    using dst_inj .
  done

lemma write_varint'_success_preserves_typing_buf_valid:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_ok: "buf_valid s buf dst_n"
      and dst_no_overflow: "unat pos + unat n < 2 ^ 32"
      and dst_range: "unat pos + unat n \<le> dst_n"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_preserves_typing[OF size fits])
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  subgoal
    using shift_ok .
  done

lemma write_varint'_success_preserves_typing_buf_valid_le5:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_ok: "buf_valid s buf dst_n"
      and dst_no_overflow: "unat pos + unat n < 2 ^ 32"
      and dst_range: "unat pos + unat n \<le> dst_n"
      and n_le: "unat n \<le> 5"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_preserves_typing_buf_valid
    [OF size fits dst_ok dst_no_overflow dst_range])
  using n_le by (auto intro: varint_shift_ok_of_unat_le5)

lemma write_varint'_success_preserves_typing_buf_valid_bounded:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_ok: "buf_valid s buf dst_n"
      and dst_no_overflow: "unat pos + unat n < 2 ^ 32"
      and dst_range: "unat pos + unat n \<le> dst_n"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_preserves_typing_buf_valid_le5
    [OF size fits dst_ok dst_no_overflow dst_range])
  using varint_size'_le5[OF size] .

lemma write_varint'_success_writes_buf_valid:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_ok: "buf_valid s buf dst_n"
      and dst_no_overflow: "unat pos + unat n < 2 ^ 32"
      and dst_range: "unat pos + unat n \<le> dst_n"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            (\<forall>j < unat n.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              varint_byte32 v n (of_nat j)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_writes[OF size fits])
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  subgoal
    using shift_ok .
  subgoal
    using dst_inj .
  done

lemma write_varint'_success_writes_buf_valid_le5:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_ok: "buf_valid s buf dst_n"
      and dst_no_overflow: "unat pos + unat n < 2 ^ 32"
      and dst_range: "unat pos + unat n \<le> dst_n"
      and n_le: "unat n \<le> 5"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            (\<forall>j < unat n.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              varint_byte32 v n (of_nat j)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_writes_buf_valid
    [OF size fits dst_ok dst_no_overflow dst_range _ dst_inj])
  using n_le by (auto intro: varint_shift_ok_of_unat_le5)

lemma write_varint'_success_writes_buf_valid_bounded:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_ok: "buf_valid s buf dst_n"
      and dst_no_overflow: "unat pos + unat n < 2 ^ 32"
      and dst_range: "unat pos + unat n \<le> dst_n"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            (\<forall>j < unat n.
              heap_w8 t (buf +\<^sub>p uint (pos + of_nat j)) =
              varint_byte32 v n (of_nat j)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_writes_buf_valid_le5
    [OF size fits dst_ok dst_no_overflow dst_range _ dst_inj])
  using varint_size'_le5[OF size] .

lemma write_varint'_success_writes_heap_bytes_word_buf_valid:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_ok: "buf_valid s buf dst_n"
      and dst_no_overflow: "unat pos + unat n < 2 ^ 32"
      and dst_range: "unat pos + unat n \<le> dst_n"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes_word t buf pos n = varint_bytes32 v n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_writes_heap_bytes_word[OF size fits])
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  subgoal
    using dst_inj .
  done

lemma write_varint'_success_decodes_heap_bytes_word_buf_valid:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_ok: "buf_valid s buf dst_n"
      and dst_no_overflow: "unat pos + unat n < 2 ^ 32"
      and dst_range: "unat pos + unat n \<le> dst_n"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes_word t buf pos n = varint_bytes32 v n \<and>
                   varint_decode (heap_bytes_word t buf pos n @ rest) =
                     Some (unat v, rest) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_varint'_success_writes_heap_bytes_word_buf_valid
      [OF size fits dst_ok dst_no_overflow dst_range dst_inj]])
  using heap_bytes_word_varint_decode[OF size, of _ buf pos rest]
  by auto

lemma write_bytes'_success_copies_heap_bytes_word_buf_valid:
  assumes fits: "\<not> cap - pos < len"
      and dst_ok: "buf_valid s buf dst_n"
      and src_ok: "buf_valid s src src_n"
      and dst_no_overflow: "unat pos + unat len < 2 ^ 32"
      and src_no_overflow: "unat src_off + unat len < 2 ^ 32"
      and dst_range: "unat pos + unat len \<le> dst_n"
      and src_range: "unat src_off + unat len \<le> src_n"
      and dst_src_disj: "\<forall>i < unat len. \<forall>j < unat len.
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           src +\<^sub>p uint (src_off + of_nat j)"
      and dst_inj: "\<forall>i < unat len. \<forall>j < unat len.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes_word t buf pos len =
                   heap_bytes_word s src src_off len \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_bytes'_success_copies_heap_bytes_word[OF fits])
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  subgoal
    using assms by (auto intro: buf_valid_word_rangeD)
  subgoal
    using dst_src_disj .
  subgoal
    using dst_inj .
  done

lemma buf_valid_shift:
  assumes ok: "buf_valid s buf (off + n)"
  shows "buf_valid s (buf +\<^sub>p int off) n"
proof (unfold buf_valid_def, intro allI impI)
  fix i
  assume i_lt: "i < n"
  have off_i_lt: "off + i < off + n"
    using i_lt by simp
  have ptr_eq: "buf +\<^sub>p int (off + i) = buf +\<^sub>p int off +\<^sub>p int i"
    by (simp add: ptr_add_def)
  show "ptr_valid (heap_typing s) (buf +\<^sub>p int off +\<^sub>p int i)"
    using buf_validD[OF ok off_i_lt] ptr_eq by simp
qed

(* ---------- State-update preservation ---------- *)

definition bufs_disjoint :: "8 word ptr \<Rightarrow> nat \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "bufs_disjoint p pn q qn =
     (\<forall>i < pn. \<forall>j < qn. p +\<^sub>p int i \<noteq> q +\<^sub>p int j)"

lemma bufs_disjoint_sym:
  "bufs_disjoint p pn q qn = bufs_disjoint q qn p pn"
  unfolding bufs_disjoint_def by (auto simp: eq_commute)

lemma bufs_disjoint_mono:
  assumes "bufs_disjoint p pn q qn"
      and "pm \<le> pn"
      and "qm \<le> qn"
  shows "bufs_disjoint p pm q qm"
  using assms by (auto simp: bufs_disjoint_def)

definition ptr_range_distinct :: "8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "ptr_range_distinct buf n \<longleftrightarrow>
     distinct (map (\<lambda>i. buf +\<^sub>p int i) [0 ..< n])"

lemma ptr_range_distinct_eqD:
  assumes dist: "ptr_range_distinct buf n"
      and i_lt: "i < n"
      and j_lt: "j < n"
      and eq: "buf +\<^sub>p int i = buf +\<^sub>p int j"
  shows "i = j"
proof -
  let ?xs = "map (\<lambda>k. buf +\<^sub>p int k) [0..<n]"
  have dist_xs: "distinct ?xs"
    using dist by (simp add: ptr_range_distinct_def)
  have nth_unique:
    "\<And>a b. \<lbrakk> a < length ?xs; b < length ?xs; ?xs ! a = ?xs ! b \<rbrakk>
      \<Longrightarrow> a = b"
  proof -
    fix a b
    assume a_lt: "a < length ?xs"
       and b_lt: "b < length ?xs"
       and same: "?xs ! a = ?xs ! b"
    show "a = b"
    proof (rule ccontr)
      assume "a \<noteq> b"
      hence "?xs ! a \<noteq> ?xs ! b"
        using dist_xs a_lt b_lt by (simp add: distinct_conv_nth)
      thus False using same by simp
    qed
  qed
  have "?xs ! i = ?xs ! j"
    using i_lt j_lt eq by simp
  thus ?thesis
    using nth_unique[of i j] i_lt j_lt by simp
qed

lemma ptr_range_distinct_mono:
  assumes dist: "ptr_range_distinct buf n"
      and le: "m \<le> n"
  shows "ptr_range_distinct buf m"
  using assms
  unfolding ptr_range_distinct_def distinct_conv_nth
  by auto

lemma ptr_range_distinct_word_range_inj:
  fixes pos len :: "32 word"
    and total :: nat
  assumes dist: "ptr_range_distinct buf total"
      and no_overflow: "unat pos + unat len < 2 ^ 32"
      and in_range: "unat pos + unat len \<le> total"
      and i_lt: "i < unat len"
      and j_lt: "j < unat len"
      and ptr_eq:
        "buf +\<^sub>p uint (pos + of_nat i) =
         buf +\<^sub>p uint (pos + of_nat j)"
  shows "i = j"
proof -
  have idx_i: "unat (pos + of_nat i :: 32 word) = unat pos + i"
    by (rule unat_add_of_nat_index[OF i_lt no_overflow])
  have idx_j: "unat (pos + of_nat j :: 32 word) = unat pos + j"
    by (rule unat_add_of_nat_index[OF j_lt no_overflow])
  have i_total: "unat pos + i < total"
    using i_lt in_range by simp
  have j_total: "unat pos + j < total"
    using j_lt in_range by simp
  have ptr_eq_nat:
    "buf +\<^sub>p int (unat pos + i) =
     buf +\<^sub>p int (unat pos + j)"
    using ptr_eq idx_i idx_j by (simp only: uint_nat)
  have "unat pos + i = unat pos + j"
    by (rule ptr_range_distinct_eqD[OF dist i_total j_total ptr_eq_nat])
  thus ?thesis by simp
qed

lemma ptr_range_distinct_word_prefix_disj:
  fixes pos len :: "32 word"
    and total :: nat
  assumes dist: "ptr_range_distinct buf total"
      and no_overflow: "unat pos + unat len < 2 ^ 32"
      and in_range: "unat pos + unat len \<le> total"
      and k_lt: "k < unat pos"
      and i_lt: "i < len"
  shows "buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
proof
  assume eq: "buf +\<^sub>p int k = buf +\<^sub>p uint (pos + i)"
  have i_nat_lt: "unat i < unat len"
    using i_lt by (simp add: word_less_nat_alt)
  have idx_i: "unat (pos + of_nat (unat i) :: 32 word) = unat pos + unat i"
    by (rule unat_add_of_nat_index[OF i_nat_lt no_overflow])
  have i_total: "unat pos + unat i < total"
    using i_nat_lt in_range by simp
  have k_total: "k < total"
    using k_lt in_range by simp
  have pos_i: "pos + of_nat (unat i) = pos + i"
    by (simp add: word_unat.Rep_inverse)
  have eq_nat:
    "buf +\<^sub>p int k = buf +\<^sub>p int (unat pos + unat i)"
    using eq idx_i pos_i by (simp only: uint_nat)
  have k_eq: "k = unat pos + unat i"
    by (rule ptr_range_distinct_eqD[OF dist k_total i_total eq_nat])
  then show False
    using k_lt by simp
qed

lemma ptr_range_distinct_lastD:
  assumes dist: "ptr_range_distinct buf (Suc n)"
      and i_lt: "i < n"
  shows "buf +\<^sub>p int i \<noteq> buf +\<^sub>p int n"
proof
  assume eq: "buf +\<^sub>p int i = buf +\<^sub>p int n"
  have "i = n"
    using ptr_range_distinct_eqD[OF dist, of i n] i_lt eq by simp
  thus False using i_lt by simp
qed

lemma heap_bytes_update_disjoint:
  assumes disj: "bufs_disjoint buf n (Ptr (ptr_val ptr)) 1"
  shows "heap_bytes (heap_w8_update (\<lambda>h. h(ptr := v)) s) buf n =
         heap_bytes s buf n"
proof -
  have "\<forall>i < n. buf +\<^sub>p int i \<noteq> ptr"
  proof (intro allI impI)
    fix i
    assume "i < n"
    from disj have "buf +\<^sub>p int i \<noteq> Ptr (ptr_val ptr) +\<^sub>p int 0"
      unfolding bufs_disjoint_def using \<open>i < n\<close> by auto
    thus "buf +\<^sub>p int i \<noteq> ptr" by simp
  qed
  thus ?thesis
    by (simp add: heap_bytes_def fun_upd_apply)
qed

lemma heap_bytes_update_outside:
  assumes "\<forall>i < n. buf +\<^sub>p int i \<noteq> ptr"
  shows "heap_bytes (heap_w8_update (\<lambda>h. h(ptr := v)) s) buf n =
         heap_bytes s buf n"
  using assms by (simp add: heap_bytes_def fun_upd_apply)

lemma write_byte'_success_preserves_heap_bytes:
  assumes pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and disj: "\<forall>i < out_n. out +\<^sub>p int i \<noteq> buf +\<^sub>p uint pos"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t out out_n = heap_bytes s out out_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[OF write_byte'_spec])
  subgoal
    using ptr_ok .
  subgoal
    using pos_lt disj by (auto simp: word_not_le heap_bytes_def fun_upd_apply)
  done

lemma write_varint_loop_preserves_heap_bytes:
  fixes len pos :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < len \<longrightarrow>
           7 * len - 7 - 7 * i < (0x20 :: 32 word)"
      and disj: "\<forall>k < out_n. \<forall>i.
           i < len \<longrightarrow> out +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. i < len)
           (\<lambda>i. do {
              guard (\<lambda>st. 7 * len - 7 - 7 * i < (0x20 :: 32 word));
              guard (\<lambda>st. ptr_valid (heap_typing st) (buf +\<^sub>p uint (pos + i)));
              modify (heap_w8_update
                (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                  if i + 1 < len
                  then (ucast
                    ((ucast
                      (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word) :: 32 word) || 0x80) :: 8 word)
                  else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word))));
              return (i + 1)
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result len \<and>
            heap_bytes t out out_n = heap_bytes s out out_n \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len
             \<and> heap_bytes st out out_n = heap_bytes s out out_n
             \<and> heap_typing st = heap_typing s"])
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
    have shift: "7 * len - 7 - 7 * i < (0x20 :: 32 word)"
      using shift_ok[rule_format, OF i_word] .
    have out_update:
      "heap_bytes
        (heap_w8_update
          (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
            if i + 1 < len
            then (ucast
              ((ucast
                (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                  :: 8 word) :: 32 word) || 0x80) :: 8 word)
            else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                  :: 8 word))) st)
        out out_n =
       heap_bytes st out out_n"
      using disj i_word
      by (auto simp: heap_bytes_def fun_upd_apply)
    show ?thesis
      using prems dst shift out_update i_word
      by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                     word_less_nat_alt word_unat.Rep_inverse
               intro: unat_suc_le_of_word_less
                      unat_measure_decrease_of_word_less)
  qed
  done

lemma write_varint'_success_preserves_heap_bytes:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
      and disj: "\<forall>k < out_n. \<forall>i.
           i < n \<longrightarrow> out +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t out out_n = heap_bytes s out out_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_varint'_def
  apply runs_to_vcg
  using size fits
  apply simp
  apply runs_to_vcg
  apply (rule runs_to_weaken[
    OF write_varint_loop_preserves_heap_bytes
      [OF dst_valid shift_ok disj]])
  by auto

lemma write_varint'_success_preserves_heap_bytes_bounded:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and disj: "\<forall>k < out_n. \<forall>i.
           i < n \<longrightarrow> out +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t out out_n = heap_bytes s out out_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_preserves_heap_bytes
    [OF size fits dst_valid _ disj])
  using varint_size'_shift_ok[OF size] by auto

lemma write_varint_loop_preserves_heap_bytes_word:
  fixes len pos out_pos out_len :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < len \<longrightarrow>
           7 * len - 7 - 7 * i < (0x20 :: 32 word)"
      and disj: "\<forall>k < unat out_len. \<forall>i.
           i < len \<longrightarrow>
           out +\<^sub>p uint (out_pos + of_nat k) \<noteq>
           buf +\<^sub>p uint (pos + i)"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. i < len)
           (\<lambda>i. do {
              guard (\<lambda>st. 7 * len - 7 - 7 * i < (0x20 :: 32 word));
              guard (\<lambda>st. ptr_valid (heap_typing st) (buf +\<^sub>p uint (pos + i)));
              modify (heap_w8_update
                (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                  if i + 1 < len
                  then (ucast
                    ((ucast
                      (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word) :: 32 word) || 0x80) :: 8 word)
                  else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word))));
              return (i + 1)
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result len \<and>
            heap_bytes_word t out out_pos out_len =
            heap_bytes_word s out out_pos out_len \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len
             \<and> heap_bytes_word st out out_pos out_len =
                heap_bytes_word s out out_pos out_len
             \<and> heap_typing st = heap_typing s"])
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
    have shift: "7 * len - 7 - 7 * i < (0x20 :: 32 word)"
      using shift_ok[rule_format, OF i_word] .
    have out_update:
      "heap_bytes_word
        (heap_w8_update
          (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
            if i + 1 < len
            then (ucast
              ((ucast
                (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                  :: 8 word) :: 32 word) || 0x80) :: 8 word)
            else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                  :: 8 word))) st)
        out out_pos out_len =
       heap_bytes_word st out out_pos out_len"
      using disj i_word
      by (auto simp: heap_bytes_word_def fun_upd_apply)
    show ?thesis
      using prems dst shift out_update i_word
      by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                     word_less_nat_alt word_unat.Rep_inverse
               intro: unat_suc_le_of_word_less
                      unat_measure_decrease_of_word_less)
  qed
  done

lemma write_varint'_success_preserves_heap_bytes_word:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
      and disj: "\<forall>k < unat out_len. \<forall>i.
           i < n \<longrightarrow>
           out +\<^sub>p uint (out_pos + of_nat k) \<noteq>
           buf +\<^sub>p uint (pos + i)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes_word t out out_pos out_len =
                   heap_bytes_word s out out_pos out_len \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_varint'_def
  apply runs_to_vcg
  using size fits
  apply simp
  apply runs_to_vcg
  apply (rule runs_to_weaken[
    OF write_varint_loop_preserves_heap_bytes_word
      [OF dst_valid shift_ok disj]])
  by auto

lemma write_varint'_success_preserves_heap_bytes_word_bounded:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and disj: "\<forall>k < unat out_len. \<forall>i.
           i < n \<longrightarrow>
           out +\<^sub>p uint (out_pos + of_nat k) \<noteq>
           buf +\<^sub>p uint (pos + i)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes_word t out out_pos out_len =
                   heap_bytes_word s out out_pos out_len \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_preserves_heap_bytes_word
    [OF size fits dst_valid _ disj])
  using varint_size'_shift_ok[OF size] by auto

lemma write_varint_loop_preserves_near_ptr:
  fixes len pos :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < len \<longrightarrow>
           7 * len - 7 - 7 * i < (0x20 :: 32 word)"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. i < len)
           (\<lambda>i. do {
              guard (\<lambda>st. 7 * len - 7 - 7 * i < (0x20 :: 32 word));
              guard (\<lambda>st. ptr_valid (heap_typing st) (buf +\<^sub>p uint (pos + i)));
              modify (heap_w8_update
                (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                  if i + 1 < len
                  then (ucast
                    ((ucast
                      (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word) :: 32 word) || 0x80) :: 8 word)
                  else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word))));
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
          shift_ok[rule_format, of i]
    by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                   word_less_nat_alt word_unat.Rep_inverse
             intro: unat_suc_le_of_word_less
                    unat_measure_decrease_of_word_less)
  done

lemma write_varint'_success_preserves_near_ptr:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   near_ptr_'' t = near_ptr_'' s \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_varint'_def
  apply runs_to_vcg
  using size fits
  apply simp
  apply runs_to_vcg
  apply (rule runs_to_weaken[
    OF write_varint_loop_preserves_near_ptr[OF dst_valid shift_ok]])
  by auto

lemma write_varint'_success_preserves_near_ptr_bounded:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   near_ptr_'' t = near_ptr_'' s \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_preserves_near_ptr
    [OF size fits dst_valid _])
  using varint_size'_shift_ok[OF size] by auto

lemma write_bytes_loop_preserves_heap_bytes:
  fixes len pos src_off :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
      and disj: "\<forall>k < out_n. \<forall>i.
           i < len \<longrightarrow> out +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
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
            heap_bytes t out out_n = heap_bytes s out out_n \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len
             \<and> heap_bytes st out out_n = heap_bytes s out out_n
             \<and> heap_typing st = heap_typing s"])
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
    have out_update:
      "heap_bytes
        (heap_w8_update
          (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                   h (src +\<^sub>p uint (src_off + i)))) st)
        out out_n =
       heap_bytes st out out_n"
      using disj i_word
      by (auto simp: heap_bytes_def fun_upd_apply)
    show ?thesis
      using prems dst src_ptr out_update i_word
      by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                     word_less_nat_alt word_unat.Rep_inverse
               intro: unat_suc_le_of_word_less
                      unat_measure_decrease_of_word_less)
  qed
  done

lemma write_bytes'_success_preserves_heap_bytes:
  assumes fits: "\<not> cap - pos < len"
      and dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
      and disj: "\<forall>k < out_n. \<forall>i.
           i < len \<longrightarrow> out +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t out out_n = heap_bytes s out out_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  using fits
  apply simp
  apply (rule runs_to_weaken[
    OF write_bytes_loop_preserves_heap_bytes
      [OF dst_valid src_valid disj]])
  by auto

lemma write_varint_loop_preserves_heap_bytes_prefix:
  fixes len pos :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < len \<longrightarrow>
           7 * len - 7 - 7 * i < (0x20 :: 32 word)"
      and prefix_disj: "\<forall>k < prefix_n. \<forall>i.
           i < len \<longrightarrow> buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. i < len)
           (\<lambda>i. do {
              guard (\<lambda>st. 7 * len - 7 - 7 * i < (0x20 :: 32 word));
              guard (\<lambda>st. ptr_valid (heap_typing st) (buf +\<^sub>p uint (pos + i)));
              modify (heap_w8_update
                (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                  if i + 1 < len
                  then (ucast
                    ((ucast
                      (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word) :: 32 word) || 0x80) :: 8 word)
                  else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                        :: 8 word))));
              return (i + 1)
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result len \<and>
            heap_bytes t buf prefix_n = heap_bytes s buf prefix_n \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len
             \<and> heap_bytes st buf prefix_n = heap_bytes s buf prefix_n
             \<and> heap_typing st = heap_typing s"])
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
    have shift: "7 * len - 7 - 7 * i < (0x20 :: 32 word)"
      using shift_ok[rule_format, OF i_word] .
    have prefix_update:
      "heap_bytes
        (heap_w8_update
          (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
            if i + 1 < len
            then (ucast
              ((ucast
                (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                  :: 8 word) :: 32 word) || 0x80) :: 8 word)
            else (ucast ((v >> unat (7 * len - 7 - 7 * i)) && 0x7F)
                  :: 8 word))) st)
        buf prefix_n =
       heap_bytes st buf prefix_n"
      using prefix_disj i_word
      by (auto simp: heap_bytes_def fun_upd_apply)
    show ?thesis
      using prems dst shift prefix_update i_word
      by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                     word_less_nat_alt word_unat.Rep_inverse
               intro: unat_suc_le_of_word_less
                      unat_measure_decrease_of_word_less)
  qed
  done

lemma write_bytes_loop_preserves_heap_bytes_prefix:
  fixes len pos src_off :: "32 word"
  assumes dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
      and prefix_disj: "\<forall>k < prefix_n. \<forall>i.
           i < len \<longrightarrow> buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
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
            heap_bytes t buf prefix_n = heap_bytes s buf prefix_n \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat len - unat i)"
      and I = "\<lambda>i st. unat i \<le> unat len
             \<and> heap_bytes st buf prefix_n = heap_bytes s buf prefix_n
             \<and> heap_typing st = heap_typing s"])
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
    have prefix_update:
      "heap_bytes
        (heap_w8_update
          (\<lambda>h. h(buf +\<^sub>p uint (pos + i) :=
                   h (src +\<^sub>p uint (src_off + i)))) st)
        buf prefix_n =
       heap_bytes st buf prefix_n"
      using prefix_disj i_word
      by (auto simp: heap_bytes_def fun_upd_apply)
    show ?thesis
      using prems dst src_ptr prefix_update i_word
      by (auto simp: runs_to.rep_eq run_bind run_guard run_modify
                     word_less_nat_alt word_unat.Rep_inverse
               intro: unat_suc_le_of_word_less
                      unat_measure_decrease_of_word_less)
  qed
  done

lemma write_bytes'_success_preserves_heap_bytes_prefix:
  assumes fits: "\<not> cap - pos < len"
      and dst_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and src_valid: "\<forall>j < unat len.
           ptr_valid (heap_typing s) (src +\<^sub>p uint (src_off + of_nat j))"
      and prefix_disj: "\<forall>k < prefix_n. \<forall>i.
           i < len \<longrightarrow> buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t buf prefix_n = heap_bytes s buf prefix_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_bytes'_def
  apply runs_to_vcg
  using fits
  apply simp
  apply (rule runs_to_weaken[
    OF write_bytes_loop_preserves_heap_bytes_prefix
      [OF dst_valid src_valid prefix_disj]])
  by auto

lemma write_bytes'_success_heap_bytes_append:
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
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t buf (unat pos + unat len) =
                   heap_bytes s buf (unat pos) @
                   heap_bytes_word s src src_off len \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have writes:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes_word t buf pos len =
               heap_bytes_word s src src_off len \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_copies_heap_bytes_word
      [OF fits dst_valid src_valid dst_src_disj dst_inj])
  have prefix:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes t buf (unat pos) = heap_bytes s buf (unat pos) \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_preserves_heap_bytes_prefix
      [OF fits dst_valid src_valid prefix_disj])
  have combined:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           heap_bytes_word t buf pos len =
           heap_bytes_word s src src_off len \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           heap_bytes t buf (unat pos) = heap_bytes s buf (unat pos) \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using writes prefix by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    using heap_bytes_append_heap_bytes_word[OF no_overflow, of _ buf]
    by auto
qed

lemma write_bytes'_success_heap_bytes_append_src0:
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
  shows "write_bytes' buf cap pos src (0 :: 32 word) len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t buf (unat pos + unat len) =
                   heap_bytes s buf (unat pos) @
                   heap_bytes s src (unat len) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append:
    "write_bytes' buf cap pos src (0 :: 32 word) len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes t buf (unat pos + unat len) =
               heap_bytes s buf (unat pos) @
               heap_bytes_word s src (0 :: 32 word) len \<and>
               heap_typing t = heap_typing s \<rbrace>"
    apply (rule write_bytes'_success_heap_bytes_append
      [of cap pos len s buf src "(0 :: 32 word)"])
          apply (fact fits)
         apply (fact dst_valid)
        apply (fact src_valid)
       apply (fact dst_src_disj)
      apply (fact dst_inj)
     apply (fact prefix_disj)
    apply (fact no_overflow)
    done
  show ?thesis
    apply (rule runs_to_weaken[OF append])
    by (simp add: heap_bytes_word_zero)
qed

lemma write_bytes'_success_heap_bytes_append_wordpos:
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
  shows "write_bytes' buf cap pos src src_off len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + len)) =
                   heap_bytes s buf (unat pos) @
                   heap_bytes_word s src src_off len \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_bytes'_success_heap_bytes_append
      [OF fits dst_valid src_valid dst_src_disj dst_inj prefix_disj no_overflow]])
  using no_overflow by (simp add: unat_word_add_no_overflow)

lemma write_bytes'_success_heap_bytes_append_src0_wordpos:
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
  shows "write_bytes' buf cap pos src (0 :: 32 word) len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + len)) =
                   heap_bytes s buf (unat pos) @
                   heap_bytes s src (unat len) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_bytes'_success_heap_bytes_append_src0
      [OF fits dst_valid src_valid dst_src_disj dst_inj prefix_disj no_overflow]])
  using no_overflow by (simp add: unat_word_add_no_overflow)

lemma write_bytes'_success_heap_bytes_append_wordpos_preserves2:
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
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes t buf (unat (pos + len)) =
               heap_bytes s buf (unat pos) @
               heap_bytes_word s src src_off len \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_heap_bytes_append_wordpos
      [OF fits dst_valid src_valid dst_src_disj dst_inj prefix_disj no_overflow])
  have pres1:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_preserves_heap_bytes
      [OF fits dst_valid src_valid disj1])
  have pres2:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + len) ENC_OK) \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_bytes'_success_preserves_heap_bytes
      [OF fits dst_valid src_valid disj2])
  have combined12:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           heap_bytes t buf (unat (pos + len)) =
           heap_bytes s buf (unat pos) @
           heap_bytes_word s src src_off len \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append pres1 by (simp add: runs_to_conj)
  have combined:
    "write_bytes' buf cap pos src src_off len \<bullet> s
       \<lbrace> \<lambda>r t.
          ((r = Result (wr_t_C (pos + len) ENC_OK) \<and>
            heap_bytes t buf (unat (pos + len)) =
            heap_bytes s buf (unat pos) @
            heap_bytes_word s src src_off len \<and>
            heap_typing t = heap_typing s) \<and>
           (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
            heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
            heap_typing t = heap_typing s)) \<and>
          (r = Result (wr_t_C (pos + len) ENC_OK) \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using combined12 pres2 by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma write_varint'_success_preserves_heap_bytes_prefix:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
      and prefix_disj: "\<forall>k < prefix_n. \<forall>i.
           i < n \<longrightarrow> buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf prefix_n = heap_bytes s buf prefix_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding write_varint'_def
  apply runs_to_vcg
  using size fits
  apply simp
  apply runs_to_vcg
  apply (rule runs_to_weaken[
    OF write_varint_loop_preserves_heap_bytes_prefix
      [OF dst_valid shift_ok prefix_disj]])
  by auto

lemma write_varint'_success_heap_bytes_append:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and shift_ok: "\<forall>i. i < n \<longrightarrow>
           7 * n - 7 - 7 * i < (0x20 :: 32 word)"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
      and prefix_disj: "\<forall>k < unat pos. \<forall>i.
           i < n \<longrightarrow> buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and no_overflow: "unat pos + unat n < 2 ^ 32"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat pos + unat n) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have writes:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes_word t buf pos n = varint_bytes32 v n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_writes_heap_bytes_word
      [OF size fits dst_valid dst_inj])
  have prefix:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes t buf (unat pos) = heap_bytes s buf (unat pos) \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes_prefix
      [OF size fits dst_valid shift_ok prefix_disj])
  have combined:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes_word t buf pos n = varint_bytes32 v n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes t buf (unat pos) = heap_bytes s buf (unat pos) \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using writes prefix by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    using heap_bytes_append_heap_bytes_word[OF no_overflow, of _ buf]
    by auto
qed

lemma write_varint'_success_heap_bytes_append_le5:
  assumes size: "varint_size' v s = Some n"
      and fits: "\<not> cap - pos < n"
      and dst_valid: "\<forall>j < unat n.
           ptr_valid (heap_typing s) (buf +\<^sub>p uint (pos + of_nat j))"
      and n_le: "unat n \<le> 5"
      and dst_inj: "\<forall>i < unat n. \<forall>j < unat n.
           i \<noteq> j \<longrightarrow>
           buf +\<^sub>p uint (pos + of_nat i) \<noteq>
           buf +\<^sub>p uint (pos + of_nat j)"
      and prefix_disj: "\<forall>k < unat pos. \<forall>i.
           i < n \<longrightarrow> buf +\<^sub>p int k \<noteq> buf +\<^sub>p uint (pos + i)"
      and no_overflow: "unat pos + unat n < 2 ^ 32"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat pos + unat n) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_heap_bytes_append
    [OF size fits dst_valid _ dst_inj prefix_disj no_overflow])
  using n_le by (auto intro: varint_shift_ok_of_unat_le5)

lemma write_varint'_success_heap_bytes_append_bounded:
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
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat pos + unat n) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule write_varint'_success_heap_bytes_append_le5
    [OF size fits dst_valid _ dst_inj prefix_disj no_overflow])
  using varint_size'_le5[OF size] .

lemma write_varint'_success_heap_bytes_append_decodes:
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
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat pos + unat n) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   varint_decode
                    (drop (unat pos)
                      (heap_bytes t buf (unat pos + unat n)) @ rest) =
                   Some (unat v, rest) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_varint'_success_heap_bytes_append_bounded
      [OF size fits dst_valid dst_inj prefix_disj no_overflow]])
  using varint_decode_varint_bytes32[OF size, of rest]
  by auto

lemma write_varint'_success_heap_bytes_append_wordpos:
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
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + n)) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_varint'_success_heap_bytes_append_bounded
      [OF size fits dst_valid dst_inj prefix_disj no_overflow]])
  using no_overflow by (simp add: unat_word_add_no_overflow)

lemma write_varint'_success_heap_bytes_append_wordpos_decodes:
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
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + n)) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   varint_decode
                    (drop (unat pos)
                      (heap_bytes t buf (unat (pos + n))) @ rest) =
                   Some (unat v, rest) \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_varint'_success_heap_bytes_append_wordpos
      [OF size fits dst_valid dst_inj prefix_disj no_overflow]])
  using varint_decode_varint_bytes32[OF size, of rest]
        no_overflow
  by (simp add: unat_word_add_no_overflow)

lemma write_varint'_success_heap_bytes_append_wordpos_preserves2:
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
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + n)) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes t buf (unat (pos + n)) =
               heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_heap_bytes_append_wordpos
      [OF size fits dst_valid dst_inj prefix_disj no_overflow])
  have pres1:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes_bounded
      [OF size fits dst_valid disj1])
  have pres2:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes_bounded
      [OF size fits dst_valid disj2])
  have combined12:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes t buf (unat (pos + n)) =
           heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append pres1 by (simp add: runs_to_conj)
  have combined:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t.
          ((r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            heap_bytes t buf (unat (pos + n)) =
            heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
            heap_typing t = heap_typing s) \<and>
           (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
            heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
            heap_typing t = heap_typing s)) \<and>
          (r = Result (wr_t_C (pos + n) ENC_OK) \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using combined12 pres2 by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma write_varint'_success_heap_bytes_append_wordpos_preserves2_word:
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
      and word_disj: "\<forall>k < unat out3_len. \<forall>i.
           i < n \<longrightarrow>
           out3 +\<^sub>p uint (out3_pos + of_nat k) \<noteq>
           buf +\<^sub>p uint (pos + i)"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + n)) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   heap_bytes_word t out3 out3_pos out3_len =
                   heap_bytes_word s out3 out3_pos out3_len \<and>
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
               heap_bytes_word t out3 out3_pos out3_len =
               heap_bytes_word s out3 out3_pos out3_len \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_heap_bytes_word_bounded
      [OF size fits dst_valid word_disj])
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
           heap_bytes_word t out3 out3_pos out3_len =
           heap_bytes_word s out3 out3_pos out3_len \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append2 pres3 by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma write_varint'_success_heap_bytes_append_wordpos_preserves2_near_ptr:
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
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + n)) =
                   heap_bytes s buf (unat pos) @ varint_bytes32 v n \<and>
                   heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
                   heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
                   near_ptr_'' t = near_ptr_'' s \<and>
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
  have near:
    "write_varint' buf cap pos v \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + n) ENC_OK) \<and>
               near_ptr_'' t = near_ptr_'' s \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_varint'_success_preserves_near_ptr_bounded
      [OF size fits dst_valid])
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
           near_ptr_'' t = near_ptr_'' s \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append2 near by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma heap_bytes_update_at_distinct:
  assumes dist: "ptr_range_distinct buf n"
      and k_lt: "k < n"
  shows "heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int k := v)) s) buf n =
         (heap_bytes s buf n)[k := v]"
proof (rule nth_equalityI)
  show "length (heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int k := v)) s) buf n) =
        length ((heap_bytes s buf n)[k := v])"
    by simp
next
  fix i
  assume i_lt_len:
    "i < length (heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int k := v)) s) buf n)"
  hence i_lt: "i < n" by simp
  show "heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int k := v)) s) buf n ! i =
        (heap_bytes s buf n)[k := v] ! i"
  proof (cases "i = k")
    case True
    thus ?thesis using i_lt k_lt
      by (simp add: heap_bytes_nth fun_upd_apply)
  next
    case False
    have ptr_ne: "buf +\<^sub>p int i \<noteq> buf +\<^sub>p int k"
    proof
      assume eq: "buf +\<^sub>p int i = buf +\<^sub>p int k"
      hence "i = k"
        using ptr_range_distinct_eqD[OF dist i_lt k_lt] by simp
      thus False using False by simp
    qed
    show ?thesis using i_lt k_lt False ptr_ne
      by (simp add: heap_bytes_nth fun_upd_apply)
  qed
qed

lemma buf_valid_heap_w8_update[simp]:
  "buf_valid (heap_w8_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma ptr_valid_heap_w8_update[simp]:
  "ptr_valid (heap_typing (heap_w8_update f s)) p =
   ptr_valid (heap_typing s) p"
  by simp

lemma heap_bytes_extend:
  assumes disj: "\<forall>i < n. buf +\<^sub>p int i \<noteq> buf +\<^sub>p int n"
  shows "heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int n := v)) s) buf (Suc n) =
         heap_bytes s buf n @ [v]"
proof (rule nth_equalityI)
  show "length (heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int n := v)) s) buf (Suc n)) =
        length (heap_bytes s buf n @ [v])"
    by simp
next
  fix i
  assume "i < length (heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int n := v)) s) buf (Suc n))"
  hence i_bound: "i < Suc n" by simp
  show "heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int n := v)) s) buf (Suc n) ! i =
        (heap_bytes s buf n @ [v]) ! i"
  proof (cases "i < n")
    case True
    hence ne: "buf +\<^sub>p int i \<noteq> buf +\<^sub>p int n" using disj by auto
    show ?thesis using True ne
      by (simp add: heap_bytes_def nth_append fun_upd_apply)
  next
    case False
    hence "i = n" using i_bound by simp
    thus ?thesis
      by (simp add: heap_bytes_def nth_append fun_upd_apply)
  qed
qed

lemma heap_bytes_extend_distinct:
  assumes "ptr_range_distinct buf (Suc n)"
  shows "heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int n := v)) s) buf (Suc n) =
         heap_bytes s buf n @ [v]"
  using assms ptr_range_distinct_lastD
  by (intro heap_bytes_extend) blast

lemma write_byte'_heap_bytes_append:
  assumes pos_nat: "unat pos = n"
      and pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and dist: "ptr_range_distinct buf (Suc n)"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t buf (Suc n) = heap_bytes s buf n @ [b] \<rbrace>"
  apply (rule runs_to_weaken[OF write_byte'_spec])
  using assms heap_bytes_extend_distinct[OF dist, of b s]
  by (auto simp: word_not_le uint_nat)

lemma write_byte'_heap_bytes_append_current:
  assumes pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and dist: "ptr_range_distinct buf (Suc (unat pos))"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t buf (Suc (unat pos)) =
                   heap_bytes s buf (unat pos) @ [b] \<rbrace>"
proof -
  have pos_nat: "unat pos = unat pos"
    by simp
  show ?thesis
    by (rule write_byte'_heap_bytes_append
      [OF pos_nat pos_lt ptr_ok dist])
qed

lemma write_byte'_heap_bytes_append_current_typing:
  assumes pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and dist: "ptr_range_distinct buf (Suc (unat pos))"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t buf (Suc (unat pos)) =
                   heap_bytes s buf (unat pos) @ [b] \<and>
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes t buf (Suc (unat pos)) =
               heap_bytes s buf (unat pos) @ [b] \<rbrace>"
    by (rule write_byte'_heap_bytes_append_current[OF pos_lt ptr_ok dist])
  have typing:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes_word t buf pos 1 = [b] \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_success_heap_bytes_word_single[OF pos_lt ptr_ok])
  have combined:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes t buf (Suc (unat pos)) =
           heap_bytes s buf (unat pos) @ [b]) \<and>
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes_word t buf pos 1 = [b] \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append typing by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma write_byte'_heap_bytes_append_next_typing:
  assumes pos_lt: "pos < cap"
      and ptr_ok: "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
      and dist: "ptr_range_distinct buf (Suc (unat pos))"
  shows "write_byte' buf cap pos b \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
                   heap_bytes t buf (unat (pos + 1)) =
                   heap_bytes s buf (unat pos) @ [b] \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF write_byte'_heap_bytes_append_current_typing
      [OF pos_lt ptr_ok dist]])
  using unat_word_suc_of_less[OF pos_lt] by simp

lemma write_byte'_heap_bytes_append_next_typing_preserves2:
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
                   heap_typing t = heap_typing s \<rbrace>"
proof -
  have append:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes t buf (unat (pos + 1)) =
               heap_bytes s buf (unat pos) @ [b] \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_heap_bytes_append_next_typing
      [OF pos_lt ptr_ok dist])
  have pres1:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_success_preserves_heap_bytes
      [OF pos_lt ptr_ok disj1])
  have pres2:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t. r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
               heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
               heap_typing t = heap_typing s \<rbrace>"
    by (rule write_byte'_success_preserves_heap_bytes
      [OF pos_lt ptr_ok disj2])
  have combined12:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes t buf (unat (pos + 1)) =
           heap_bytes s buf (unat pos) @ [b] \<and>
           heap_typing t = heap_typing s) \<and>
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using append pres1 by (simp add: runs_to_conj)
  have combined:
    "write_byte' buf cap pos b \<bullet> s
       \<lbrace> \<lambda>r t.
          ((r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
            heap_bytes t buf (unat (pos + 1)) =
            heap_bytes s buf (unat pos) @ [b] \<and>
            heap_typing t = heap_typing s) \<and>
           (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
            heap_bytes t out1 out1_n = heap_bytes s out1 out1_n \<and>
            heap_typing t = heap_typing s)) \<and>
          (r = Result (wr_t_C (pos + 1) ENC_OK) \<and>
           heap_bytes t out2 out2_n = heap_bytes s out2 out2_n \<and>
           heap_typing t = heap_typing s) \<rbrace>"
    using combined12 pres2 by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

end

end
