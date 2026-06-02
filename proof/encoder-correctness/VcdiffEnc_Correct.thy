(*
  Success-path correctness scaffolding for the AutoCorres-lifted C encoder.

  Target shape:

    vcdiff_encode' returns patch_len > 0
      ==> decode_spec emitted_patch source = Inl target

  This avoids proving byte identity against encode_spec: the C encoder emits
  RUN, COPY, and fused ADD+COPY opcodes, while the current pure encoder emits
  only standalone opcodes.
*)
theory VcdiffEnc_Correct
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

(* ---------- Buffer-to-list conversion ---------- *)

definition heap_bytes :: "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> byte list" where
  "heap_bytes s buf n = map (\<lambda>i. heap_w8 s (buf +\<^sub>p int i)) [0 ..< n]"

lemma heap_bytes_length[simp]:
  "length (heap_bytes s buf n) = n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_nth:
  "i < n \<Longrightarrow> heap_bytes s buf n ! i = heap_w8 s (buf +\<^sub>p int i)"
  by (simp add: heap_bytes_def)

lemma heap_bytes_eqI:
  assumes "\<And>i. i < n \<Longrightarrow> heap_w8 t (buf +\<^sub>p int i) = heap_w8 s (buf +\<^sub>p int i)"
  shows "heap_bytes t buf n = heap_bytes s buf n"
  using assms by (auto simp: heap_bytes_def)

lemma write_varint'_overflow_preserves_heap_bytes:
  assumes size: "varint_size' v s = Some n"
      and overflow: "cap - pos < n"
  shows "write_varint' buf cap pos v \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (wr_t_C pos ENC_OVERFLOW) \<and>
                   heap_bytes t out out_n = heap_bytes s out out_n \<rbrace>"
  apply (rule runs_to_weaken[OF write_varint'_overflow[OF size overflow]])
  by auto

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
