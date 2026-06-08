theory VcdiffEnc_Match
  imports
    VcdiffEnc_Cache_Opcode
begin


(*
  Match-quality predicate used by the future find_best_match proof: either
  no usable match was returned, or the source and target slices are equal.
*)
definition match_valid :: "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "match_valid src tgt tp pos len \<longleftrightarrow>
     (len = 0 \<or>
      pos + len \<le> length src \<and>
      tp + len \<le> length tgt \<and>
      take len (drop pos src) = take len (drop tp tgt))"

lemma match_valid_zero[simp]:
  "match_valid src tgt tp pos 0"
  by (simp add: match_valid_def)

lemma match_validI:
  assumes "pos + len \<le> length src"
      and "tp + len \<le> length tgt"
      and "take len (drop pos src) = take len (drop tp tgt)"
  shows "match_valid src tgt tp pos len"
  using assms by (simp add: match_valid_def)

lemma match_validD:
  assumes "match_valid src tgt tp pos len"
      and "len \<noteq> 0"
  shows "pos + len \<le> length src"
        "tp + len \<le> length tgt"
        "take len (drop pos src) = take len (drop tp tgt)"
  using assms by (simp_all add: match_valid_def)

context vcdiff_enc_global_addresses begin

lemma match_valid_heap_bytesI:
  assumes src_bound: "pos + len \<le> src_len"
      and tgt_bound: "tp + len \<le> tgt_len"
      and bytes_eq: "\<And>i. i < len \<Longrightarrow>
        heap_w8 s (src +\<^sub>p int (pos + i)) =
        heap_w8 s (tgt +\<^sub>p int (tp + i))"
  shows "match_valid (heap_bytes s src src_len) (heap_bytes s tgt tgt_len)
           tp pos len"
proof (rule match_validI)
  show "pos + len \<le> length (heap_bytes s src src_len)"
    using src_bound by simp
  show "tp + len \<le> length (heap_bytes s tgt tgt_len)"
    using tgt_bound by simp
  show "take len (drop pos (heap_bytes s src src_len)) =
        take len (drop tp (heap_bytes s tgt tgt_len))"
  proof (rule nth_equalityI)
    show "length (take len (drop pos (heap_bytes s src src_len))) =
          length (take len (drop tp (heap_bytes s tgt tgt_len)))"
      using src_bound tgt_bound by simp
  next
    fix i
    assume i_lt: "i < length (take len (drop pos (heap_bytes s src src_len)))"
    hence i_len: "i < len"
      by simp
    have src_i: "pos + i < src_len"
      using src_bound i_len by simp
    have tgt_i: "tp + i < tgt_len"
      using tgt_bound i_len by simp
    show "take len (drop pos (heap_bytes s src src_len)) ! i =
          take len (drop tp (heap_bytes s tgt tgt_len)) ! i"
      using i_len src_i tgt_i bytes_eq[OF i_len]
      by (simp add: heap_bytes_nth)
  qed
qed

lemma match_valid_heap_bytes_wordI:
  fixes tp pos len :: "32 word"
  assumes src_bound: "unat pos + unat len \<le> src_len"
      and tgt_bound: "unat tp + unat len \<le> tgt_len"
      and src_no_overflow: "unat pos + unat len < 2 ^ 32"
      and tgt_no_overflow: "unat tp + unat len < 2 ^ 32"
      and bytes_eq: "\<And>i. i < unat len \<Longrightarrow>
        heap_w8 s (src +\<^sub>p uint (pos + of_nat i :: 32 word)) =
        heap_w8 s (tgt +\<^sub>p uint (tp + of_nat i :: 32 word))"
  shows "match_valid (heap_bytes s src src_len) (heap_bytes s tgt tgt_len)
           (unat tp) (unat pos) (unat len)"
proof (rule match_valid_heap_bytesI)
  show "unat pos + unat len \<le> src_len"
    using src_bound .
  show "unat tp + unat len \<le> tgt_len"
    using tgt_bound .
  fix i
  assume i_lt: "i < unat len"
  have src_idx:
    "unat (pos + of_nat i :: 32 word) = unat pos + i"
    by (rule unat_add_of_nat_index[OF i_lt src_no_overflow])
  have tgt_idx:
    "unat (tp + of_nat i :: 32 word) = unat tp + i"
    by (rule unat_add_of_nat_index[OF i_lt tgt_no_overflow])
  show "heap_w8 s (src +\<^sub>p int (unat pos + i)) =
        heap_w8 s (tgt +\<^sub>p int (unat tp + i))"
    using bytes_eq[OF i_lt]
    by (simp only: src_idx[symmetric] tgt_idx[symmetric] uint_nat)
qed

lemma heap_bytes_heap_w32_update[simp]:
  "heap_bytes (heap_w32_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_w8_heap_w32_update[simp]:
  "heap_w8 (heap_w32_update f s) p = heap_w8 s p"
  by simp

lemma buf_valid_heap_w32_update[simp]:
  "buf_valid (heap_w32_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma hash4'_heap_w32_update[simp]:
  "hash4' buf pos (heap_w32_update f s) = hash4' buf pos s"
  unfolding hash4'_def
  by (simp add: obind_def ogets_def oguard_def)

lemma checked_measure_decreases:
  fixes checked :: "32 word"
  assumes "checked < 0x10"
  shows "16 - unat (checked + 1) < 16 - unat checked"
proof -
  have checked_lt: "unat checked < 16"
    using assms by (simp add: word_less_nat_alt)
  hence no_overflow: "unat checked + unat (1 :: 32 word) < 2 ^ 32"
    by simp
  have unat_suc: "unat (checked + 1) = Suc (unat checked)"
    using no_overflow by (simp add: unat_word_ariths(1))
  show ?thesis
    using checked_lt by (simp add: unat_suc)
qed


lemma find_best_match'_match_valid_if_common_prefix:
  assumes common_prefix_valid:
    "\<And>cand l. common_prefix' src cand src_len tgt tp tgt_len s = Some l \<Longrightarrow>
       match_valid src_bytes tgt_bytes (unat tp) (unat cand) (unat l)"
      and result:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m"
  shows "match_valid src_bytes tgt_bytes (unat tp)
           (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
proof -
  let ?C = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word) s.
      cand \<noteq> 0xFFFFFFFF \<and> checked < 0x10"
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
  have loop_preserves:
    "\<And>init. (case init of (best_len, best_pos, cand, checked) \<Rightarrow>
        match_valid src_bytes tgt_bytes (unat tp)
          (unat best_pos) (unat best_len)) \<Longrightarrow>
      case owhile ?C ?B init s of
        None \<Rightarrow> True
      | Some (best_len, best_pos, cand, checked) \<Rightarrow>
          match_valid src_bytes tgt_bytes (unat tp)
            (unat best_pos) (unat best_len)"
    apply (rule Reader_Monad.owhile_rule[
      where I = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                     cand :: 32 word, checked :: 32 word) s.
          match_valid src_bytes tgt_bytes (unat tp)
            (unat best_pos) (unat best_len)"
        and M = "measure
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
               cand :: 32 word, checked :: 32 word). 16 - unat checked)"])
       apply (simp split: prod.splits)
      apply simp
    subgoal for r r'
      using common_prefix_valid
      apply (cases r; cases r')
      apply (auto simp: obind_def ocondition_def oreturn_def ogets_def
                        oguard_def K_def
                 intro: checked_measure_decreases
                 split: option.splits if_splits)
      done
    subgoal for r r'
      using common_prefix_valid
      apply (cases r; cases r')
      apply (auto simp: obind_def ocondition_def oreturn_def ogets_def
                        oguard_def K_def
                 split: option.splits if_splits)
      done
   apply simp
  apply (clarsimp split: prod.splits)
    done
  have loop_valid_some:
    "\<And>(init :: 32 word \<times> 32 word \<times> 32 word \<times> 32 word)
        (best_len :: 32 word) (best_pos :: 32 word)
        (cand :: 32 word) (checked :: 32 word).
      owhile ?C ?B init s =
        Some (best_len, best_pos, cand, checked) \<Longrightarrow>
      (case init of (init_len, init_pos, init_cand, init_checked) \<Rightarrow>
        match_valid src_bytes tgt_bytes (unat tp)
          (unat init_pos) (unat init_len)) \<Longrightarrow>
      match_valid src_bytes tgt_bytes (unat tp)
        (unat best_pos) (unat best_len)"
  proof -
    fix init :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    fix best_len best_pos cand checked :: "32 word"
    assume ow:
      "owhile ?C ?B init s = Some (best_len, best_pos, cand, checked)"
    assume init_inv:
      "case init of (init_len, init_pos, init_cand, init_checked) \<Rightarrow>
        match_valid src_bytes tgt_bytes (unat tp)
          (unat init_pos) (unat init_len)"
    have "case owhile ?C ?B init s of
        None \<Rightarrow> True
      | Some (best_len, best_pos, cand, checked) \<Rightarrow>
          match_valid src_bytes tgt_bytes (unat tp)
            (unat best_pos) (unat best_len)"
      using loop_preserves[OF init_inv] .
    thus "match_valid src_bytes tgt_bytes (unat tp)
        (unat best_pos) (unat best_len)"
      using ow by simp
  qed
  have loop_valid_zero_some:
    "\<And>(cand0 :: 32 word) (best_len :: 32 word) (best_pos :: 32 word)
        (cand :: 32 word) (checked :: 32 word).
      owhile ?C ?B
        ((0 :: 32 word), ((0 :: 32 word), (cand0, (0 :: 32 word)))) s =
        Some (best_len, best_pos, cand, checked) \<Longrightarrow>
      match_valid src_bytes tgt_bytes (unat tp)
        (unat best_pos) (unat best_len)"
    apply (rule loop_valid_some)
     apply assumption
    apply simp
    done
  show ?thesis
    using result
    unfolding find_best_match'_def
    apply (auto simp: obind_def ocondition_def oreturn_def ogets_def
                      oguard_def K_def
                split: option.splits prod.splits if_splits)
    subgoal for h best_len best_pos cand checked
      apply (rule loop_valid_zero_some
        [unfolded obind_def ocondition_def oreturn_def ogets_def
                  oguard_def K_def, simplified o_def])
      apply assumption
      done
    done
qed

end

end
