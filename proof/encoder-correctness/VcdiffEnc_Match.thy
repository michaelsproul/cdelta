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

lemma match_source_positions_spec_set:
  "set (source_positions_spec src) =
    (if length src < min_match then {} else {0..<length src - min_match + 1})"
  by (auto simp: source_positions_spec_def)

lemma match_source_positions_spec_sound:
  assumes "p \<in> set (source_positions_spec src)"
  shows "p + min_match \<le> length src"
proof (cases "length src < min_match")
  case True
  with assms show ?thesis
    by (simp add: source_positions_spec_def)
next
  case False
  with assms have "p < length src - min_match + 1"
    by (auto simp: source_positions_spec_def)
  then have "p \<le> length src - min_match"
    by linarith
  with False show ?thesis
    by linarith
qed

lemma match_build_index_spec_length[simp]:
  "length (build_index_spec src) = hash_size"
  by (simp add: build_index_spec_def)

lemma match_index_bucket_build_index_spec:
  assumes "h < hash_size"
  shows "index_bucket_spec (build_index_spec src) h =
    filter (\<lambda>p. hash_bucket_spec src p = h) (source_positions_spec src)"
  using assms
  by (simp add: index_bucket_spec_def build_index_spec_def)

lemma match_index_bucket_build_index_spec_out_of_range[simp]:
  assumes "\<not> h < hash_size"
  shows "index_bucket_spec (build_index_spec src) h = []"
  using assms
  by (simp add: index_bucket_spec_def)

lemma match_build_index_spec_bucket_sound:
  assumes "p \<in> set (index_bucket_spec (build_index_spec src) h)"
  shows "p + min_match \<le> length src \<and> hash_bucket_spec src p = h"
  using assms match_source_positions_spec_sound[of p src]
  by (auto simp: index_bucket_spec_def build_index_spec_def)

abbreviation no_entry32 :: "32 word" where
  "no_entry32 \<equiv> 0xFFFFFFFF"

fun match_word_chain :: "32 word list \<Rightarrow> nat \<Rightarrow> 32 word \<Rightarrow> nat list" where
  "match_word_chain next 0 cand = []"
| "match_word_chain next (Suc fuel) cand =
    (if cand = no_entry32 then []
     else if unat cand < length next then
       unat cand # match_word_chain next fuel (next ! unat cand)
     else [])"

definition heap_w32_list :: "lifted_globals \<Rightarrow> 32 word ptr \<Rightarrow> nat \<Rightarrow> 32 word list" where
  "heap_w32_list s arr n = map (\<lambda>i. heap_w32 s (arr +\<^sub>p int i)) [0..<n]"

definition source_index_arrays_rel ::
    "byte list \<Rightarrow> 32 word list \<Rightarrow> 32 word list \<Rightarrow> bool" where
  "source_index_arrays_rel src heads nexts \<longleftrightarrow>
     length heads = hash_size \<and>
     length nexts = length src \<and>
     (\<forall>h < hash_size.
       (let bucket = index_bucket_spec (build_index_spec src) h in
        if bucket = [] then heads ! h = no_entry32
        else heads ! h = of_nat (hd bucket) \<and>
             match_word_chain nexts (length bucket) (heads ! h) = bucket))"

definition source_index_heap_rel ::
    "lifted_globals \<Rightarrow> byte list \<Rightarrow> 32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow> bool" where
  "source_index_heap_rel s src head_arr next_arr \<longleftrightarrow>
     source_index_arrays_rel src
       (heap_w32_list s head_arr hash_size)
       (heap_w32_list s next_arr (length src))"

lemma heap_w32_list_length[simp]:
  "length (heap_w32_list s arr n) = n"
  by (simp add: heap_w32_list_def)

lemma heap_w32_list_nth[simp]:
  assumes "i < n"
  shows "heap_w32_list s arr n ! i = heap_w32 s (arr +\<^sub>p int i)"
  using assms by (simp add: heap_w32_list_def)

lemma heap_w32_list_update_outside:
  assumes outside: "\<forall>i < n. arr +\<^sub>p int i \<noteq> ptr"
  shows "heap_w32_list (heap_w32_update (\<lambda>h. h(ptr := v)) s) arr n =
         heap_w32_list s arr n"
  using outside by (simp add: heap_w32_list_def fun_upd_apply)

lemma source_index_arrays_rel_head_length:
  assumes "source_index_arrays_rel src heads nexts"
  shows "length heads = hash_size"
  using assms by (simp add: source_index_arrays_rel_def)

lemma source_index_arrays_rel_next_length:
  assumes "source_index_arrays_rel src heads nexts"
  shows "length nexts = length src"
  using assms by (simp add: source_index_arrays_rel_def)

lemma source_index_arrays_rel_empty_head:
  assumes rel: "source_index_arrays_rel src heads nexts"
      and h_lt: "h < hash_size"
      and empty: "index_bucket_spec (build_index_spec src) h = []"
  shows "heads ! h = no_entry32"
  using rel h_lt empty
  by (simp add: source_index_arrays_rel_def Let_def)

lemma source_index_arrays_rel_nonempty_head:
  assumes rel: "source_index_arrays_rel src heads nexts"
      and h_lt: "h < hash_size"
      and nonempty: "index_bucket_spec (build_index_spec src) h \<noteq> []"
  shows "heads ! h = of_nat (hd (index_bucket_spec (build_index_spec src) h))"
  using rel h_lt nonempty
  by (simp add: source_index_arrays_rel_def Let_def)

lemma source_index_arrays_rel_bucket_chain:
  assumes rel: "source_index_arrays_rel src heads nexts"
      and h_lt: "h < hash_size"
      and nonempty: "index_bucket_spec (build_index_spec src) h \<noteq> []"
  shows "match_word_chain nexts
           (length (index_bucket_spec (build_index_spec src) h))
           (heads ! h) =
         index_bucket_spec (build_index_spec src) h"
proof -
  let ?bucket = "index_bucket_spec (build_index_spec src) h"
  have rel_h:
    "(let bucket = ?bucket in
      if bucket = [] then heads ! h = no_entry32
      else heads ! h = of_nat (hd bucket) \<and>
           match_word_chain nexts (length bucket) (heads ! h) = bucket)"
    using rel h_lt
    unfolding source_index_arrays_rel_def by blast
  show ?thesis
  proof (cases "?bucket = []")
    case True
    with nonempty show ?thesis
      by simp
  next
    case False
    have rel_h_unlet:
      "if ?bucket = [] then heads ! h = no_entry32
       else heads ! h = of_nat (hd ?bucket) \<and>
            match_word_chain nexts (length ?bucket) (heads ! h) = ?bucket"
      using rel_h unfolding Let_def .
    from rel_h_unlet False have conj:
      "heads ! h = of_nat (hd ?bucket) \<and>
       match_word_chain nexts (length ?bucket) (heads ! h) = ?bucket"
      apply (subst (asm) if_not_P)
       apply assumption
      apply assumption
      done
    show ?thesis
      by (rule conjunct2[OF conj])
  qed
qed

lemma match_word_chain_member_bound:
  assumes "p \<in> set (match_word_chain nexts fuel cand)"
  shows "p < length nexts"
  using assms
  by (induction fuel arbitrary: cand) (auto split: if_splits)

lemma match_word_chain_take:
  "take n (match_word_chain nexts fuel cand) =
   match_word_chain nexts (min n fuel) cand"
proof (induction fuel arbitrary: n cand)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      by simp
  next
    case (Suc n')
    show ?thesis
    proof (cases "cand = no_entry32 \<or> \<not> unat cand < length nexts")
      case True
      then show ?thesis
        using Suc by (auto simp: Suc split: if_splits)
    next
      case False
      then have cand_ok: "cand \<noteq> no_entry32" "unat cand < length nexts"
        by auto
      show ?thesis
        using Suc.IH[of n' "nexts ! unat cand"] cand_ok Suc
        by simp
    qed
  qed
qed

lemma source_index_arrays_rel_bucket_chain_all:
  assumes rel: "source_index_arrays_rel src heads nexts"
      and h_lt: "h < hash_size"
  shows "match_word_chain nexts
           (length (index_bucket_spec (build_index_spec src) h))
           (heads ! h) =
         index_bucket_spec (build_index_spec src) h"
proof (cases "index_bucket_spec (build_index_spec src) h = []")
  case True
  then show ?thesis
    by simp
next
  case False
  show ?thesis
    by (rule source_index_arrays_rel_bucket_chain[OF rel h_lt False])
qed

lemma source_index_arrays_rel_take_bucket_chain:
  assumes rel: "source_index_arrays_rel src heads nexts"
      and h_lt: "h < hash_size"
  shows "match_word_chain nexts
           (min n (length (index_bucket_spec (build_index_spec src) h)))
           (heads ! h) =
         take n (index_bucket_spec (build_index_spec src) h)"
proof -
  have chain:
    "match_word_chain nexts
       (length (index_bucket_spec (build_index_spec src) h))
       (heads ! h) =
     index_bucket_spec (build_index_spec src) h"
    by (rule source_index_arrays_rel_bucket_chain_all[OF rel h_lt])
  show ?thesis
    using match_word_chain_take[
        of n nexts "length (index_bucket_spec (build_index_spec src) h)"
          "heads ! h"] chain
    by simp
qed

lemma source_index_arrays_rel_chain_member_sound:
  assumes rel: "source_index_arrays_rel src heads nexts"
      and h_lt: "h < hash_size"
      and p_in: "p \<in> set (match_word_chain nexts
        (length (index_bucket_spec (build_index_spec src) h)) (heads ! h))"
  shows "p + min_match \<le> length src \<and> hash_bucket_spec src p = h"
proof -
  have chain:
    "match_word_chain nexts
       (length (index_bucket_spec (build_index_spec src) h)) (heads ! h) =
     index_bucket_spec (build_index_spec src) h"
    by (rule source_index_arrays_rel_bucket_chain_all[OF rel h_lt])
  show ?thesis
    using p_in chain match_build_index_spec_bucket_sound[of p src h]
    by simp
qed

lemma source_index_arrays_rel_take_chain_member_sound:
  assumes rel: "source_index_arrays_rel src heads nexts"
      and h_lt: "h < hash_size"
      and p_in: "p \<in> set (match_word_chain nexts
        (min n (length (index_bucket_spec (build_index_spec src) h)))
        (heads ! h))"
  shows "p + min_match \<le> length src \<and> hash_bucket_spec src p = h"
proof -
  have chain:
    "match_word_chain nexts
       (min n (length (index_bucket_spec (build_index_spec src) h)))
       (heads ! h) =
     take n (index_bucket_spec (build_index_spec src) h)"
    by (rule source_index_arrays_rel_take_bucket_chain[OF rel h_lt])
  show ?thesis
    using p_in chain match_build_index_spec_bucket_sound[of p src h]
    by (auto dest: in_set_takeD)
qed

lemma source_index_arrays_rel_short:
  assumes src_short: "length src < min_match"
      and heads_len: "length heads = hash_size"
      and nexts_len: "length nexts = length src"
      and heads_empty: "\<And>h. h < hash_size \<Longrightarrow> heads ! h = no_entry32"
  shows "source_index_arrays_rel src heads nexts"
  unfolding source_index_arrays_rel_def
proof (intro conjI allI impI)
  show "length heads = hash_size"
    using heads_len .
  show "length nexts = length src"
    using nexts_len .
  fix h
  assume h_lt: "h < hash_size"
  have bucket_empty: "index_bucket_spec (build_index_spec src) h = []"
    using src_short h_lt
    by (simp add: index_bucket_spec_def build_index_spec_def source_positions_spec_def)
  show "let bucket = index_bucket_spec (build_index_spec src) h in
        if bucket = [] then heads ! h = no_entry32
        else heads ! h = word_of_nat (hd bucket) \<and>
             match_word_chain nexts (length bucket) (heads ! h) = bucket"
    using bucket_empty heads_empty[OF h_lt]
    by simp
qed

context vcdiff_enc_global_addresses begin

lemma hash_size_0x10000[simp]:
  "hash_size = 0x10000"
  by (simp add: hash_size_def hash_bits_def)

lemma unat_0x10000_32[simp]:
  "unat (0x10000 :: 32 word) = hash_size"
  by (simp add: hash_size_def hash_bits_def)

lemma build_index_head_init_loop:
  fixes head :: "32 word ptr"
  assumes head_valid:
    "\<And>i. i < (0x10000 :: 32 word) \<Longrightarrow>
      IS_VALID(32 word) s (head +\<^sub>p uint i)"
  shows "(whileLoop (\<lambda>(idx :: 32 word) st. idx < 0x10000)
      (\<lambda>idx. do {
          guard (\<lambda>st. IS_VALID(32 word) st (head +\<^sub>p uint idx));
          modify (heap_w32_update
            (\<lambda>h. h(head +\<^sub>p uint idx := no_entry32)));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
    \<lbrace> \<lambda>r t. r = Result (0x10000 :: 32 word)
          \<and> heap_typing t = heap_typing s
          \<and> (\<forall>h < hash_size. heap_w32 t (head +\<^sub>p int h) = no_entry32) \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((idx :: 32 word), _). hash_size - unat idx)"
      and I = "\<lambda>idx st. unat idx \<le> hash_size
          \<and> heap_typing st = heap_typing s
          \<and> (\<forall>h < unat idx. heap_w32 st (head +\<^sub>p int h) = no_entry32)"])
     subgoal by simp
    subgoal by simp
   subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal premises prems for idx st
  proof -
    have idx_lt_word: "idx < (0x10000 :: 32 word)"
      using prems(1) by (simp add: word_less_nat_alt)
    have idx_lt: "unat idx < hash_size"
      using idx_lt_word by (simp add: word_less_nat_alt)
    have idx_suc: "unat (idx + 1) = Suc (unat idx)"
      using idx_lt by (simp add: unat_word_ariths(1))
    have typing_eq: "heap_typing st = heap_typing s"
      using prems(2) by simp
    have valid_s:
      "IS_VALID(32 word) s (head +\<^sub>p uint idx)"
      by (rule head_valid[OF idx_lt_word])
    have valid_idx:
      "IS_VALID(32 word) st (head +\<^sub>p uint idx)"
      using valid_s typing_eq by simp
    show ?thesis
      apply runs_to_vcg
      subgoal
        using valid_idx .
      subgoal
        using idx_suc idx_lt by simp
      subgoal
        using typing_eq .
      subgoal premises sg for h
      proof -
        have h_lt_suc: "h < Suc (unat idx)"
          using sg(2) idx_suc by simp
        have h_ne: "h \<noteq> unat idx"
        proof
          assume h_eq: "h = unat idx"
          have offset_eq: "int h = uint idx"
            using h_eq by (simp only: uint_nat)
          hence "head +\<^sub>p int h = head +\<^sub>p uint idx"
            by simp
          with sg(1) show False
            by simp
        qed
        have h_lt: "h < unat idx"
          using h_lt_suc h_ne by simp
        show "heap_w32 st (head +\<^sub>p int h) = no_entry32"
          using prems(2) h_lt by simp
      qed
      subgoal
        using idx_suc idx_lt by simp
      done
  qed
  done

lemma build_index'_short_source_index_heap_rel:
  fixes src :: "8 word ptr"
    and src_len :: "32 word"
    and head next_arr :: "32 word ptr"
  assumes src_short: "src_len < 4"
      and head_valid:
        "\<And>i. i < (0x10000 :: 32 word) \<Longrightarrow>
          IS_VALID(32 word) s (head +\<^sub>p uint i)"
  shows "build_index' src src_len head next_arr \<bullet> s
    \<lbrace> \<lambda>r t. r = Result () \<and>
        source_index_heap_rel t (heap_bytes s src (unat src_len)) head next_arr
        \<and> heap_typing t = heap_typing s \<rbrace>"
  unfolding build_index'_def
  apply runs_to_vcg
  subgoal
    apply (rule runs_to_weaken[OF build_index_head_init_loop[OF head_valid]])
     apply simp
    using src_short
    apply (clarsimp simp: runs_to_iff source_index_heap_rel_def word_less_nat_alt min_match_def
        split: exception_or_result_splits)
    apply (rule source_index_arrays_rel_short)
       apply (simp add: min_match_def)
      apply simp
     apply (simp add: heap_w32_list_nth)
    apply simp
    done
  done

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

lemma find_best_match'_early_zero:
  assumes "src_len < 4 \<or> tgt_len - tp < 4"
  shows "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
         Some (match_t_C 0 0)"
  using assms
  unfolding find_best_match'_def
  by (auto simp: ocondition_def oreturn_def K_def)

lemma find_best_match'_early_zero_valid:
  assumes early: "src_len < 4 \<or> tgt_len - tp < 4"
  shows "\<exists>m.
     find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m \<and>
     match_valid src_bytes tgt_bytes (unat tp)
       (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
  using find_best_match'_early_zero[OF early]
  by auto

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
