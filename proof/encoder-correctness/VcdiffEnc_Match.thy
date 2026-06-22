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

definition source_positions_from ::
    "byte list \<Rightarrow> nat \<Rightarrow> nat list" where
  "source_positions_from src start =
     (if length src < min_match then []
      else [start..<length src - min_match + 1])"

definition source_index_bucket_from ::
    "byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "source_index_bucket_from src start h =
     filter (\<lambda>p. hash_bucket_spec src p = h)
       (source_positions_from src start)"

definition source_index_arrays_rel_from ::
    "byte list \<Rightarrow> nat \<Rightarrow> 32 word list \<Rightarrow> 32 word list \<Rightarrow> bool" where
  "source_index_arrays_rel_from src start heads nexts \<longleftrightarrow>
     length heads = hash_size \<and>
     length nexts = length src \<and>
     (\<forall>h < hash_size.
       (let bucket = source_index_bucket_from src start h in
        if bucket = [] then heads ! h = no_entry32
        else heads ! h = of_nat (hd bucket) \<and>
             match_word_chain nexts (length bucket) (heads ! h) = bucket))"

definition source_index_heap_rel_from ::
    "lifted_globals \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow>
      32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow> bool" where
  "source_index_heap_rel_from s src start head_arr next_arr \<longleftrightarrow>
     source_index_arrays_rel_from src start
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

lemma heap_w32_list_update_index:
  assumes idx_lt: "idx < n"
      and ptr_eq: "ptr = arr +\<^sub>p int idx"
      and no_alias:
        "\<And>i. i < n \<Longrightarrow> i \<noteq> idx \<Longrightarrow> arr +\<^sub>p int i \<noteq> ptr"
  shows "heap_w32_list (heap_w32_update (\<lambda>h. h(ptr := v)) s) arr n =
         (heap_w32_list s arr n)[idx := v]"
proof (rule nth_equalityI)
  show "length (heap_w32_list (heap_w32_update (\<lambda>h. h(ptr := v)) s) arr n) =
        length ((heap_w32_list s arr n)[idx := v])"
    by simp
  fix i
  assume i_lt:
    "i < length (heap_w32_list (heap_w32_update (\<lambda>h. h(ptr := v)) s) arr n)"
  hence i_lt_n: "i < n"
    by simp
  show "heap_w32_list (heap_w32_update (\<lambda>h. h(ptr := v)) s) arr n ! i =
        (heap_w32_list s arr n)[idx := v] ! i"
  proof (cases "i = idx")
    case True
    then show ?thesis
      using idx_lt ptr_eq by simp
  next
    case False
    have ptr_ne: "arr +\<^sub>p int i \<noteq> ptr"
      by (rule no_alias[OF i_lt_n False])
    show ?thesis
      using i_lt_n False ptr_ne by simp
  qed
qed

lemma heap_w32_update_read_current:
  "heap_w32_update (\<lambda>a. a(ptr := a src_ptr)) s =
   heap_w32_update (\<lambda>a. a(ptr := heap_w32 s src_ptr)) s"
  by simp

lemma heap_typing_heap_w32_update[simp]:
  "heap_typing (heap_w32_update f s) = heap_typing s"
  by simp

lemma holds_post_state_run_return[simp]:
  "holds_post_state P (run (return v) s) = P (Result v, s)"
proof -
  have run_eq: "run (return v) s = Success {(Result v, s)}"
    by (rule Reaches.outcomes_succeeds_run_conv)
       (rule Reaches.outcomes_return, rule Reaches.succeeds_return)
  show ?thesis
    by (simp add: run_eq)
qed

lemma hash_bucket_spec_lt[simp]:
  "hash_bucket_spec bs pos < hash_size"
  by (simp add: hash_bucket_spec_def hash_size_def hash_bits_def)

lemma source_positions_from_0[simp]:
  "source_positions_from src 0 = source_positions_spec src"
  by (simp add: source_positions_from_def source_positions_spec_def)

lemma source_index_bucket_from_0[simp]:
  "source_index_bucket_from src 0 h =
   index_bucket_spec (build_index_spec src) h"
proof (cases "h < hash_size")
  case True
  then show ?thesis
    by (simp add: source_index_bucket_from_def
        match_index_bucket_build_index_spec)
next
  case False
  have bucket_ne: "\<And>p. hash_bucket_spec src p \<noteq> h"
    using False hash_bucket_spec_lt[of src] by force
  show ?thesis
    using False bucket_ne
    by (simp add: source_index_bucket_from_def
        match_index_bucket_build_index_spec_out_of_range)
qed

lemma source_index_arrays_rel_from_0:
  "source_index_arrays_rel_from src 0 heads nexts \<longleftrightarrow>
   source_index_arrays_rel src heads nexts"
  by (simp add: source_index_arrays_rel_from_def
      source_index_arrays_rel_def)

lemma source_index_heap_rel_from_0:
  "source_index_heap_rel_from s src 0 head_arr next_arr \<longleftrightarrow>
   source_index_heap_rel s src head_arr next_arr"
  by (simp add: source_index_heap_rel_from_def source_index_heap_rel_def
      source_index_arrays_rel_from_0)

lemma source_index_arrays_rel_from_head_length:
  assumes "source_index_arrays_rel_from src start heads nexts"
  shows "length heads = hash_size"
  using assms by (simp add: source_index_arrays_rel_from_def)

lemma source_index_arrays_rel_from_next_length:
  assumes "source_index_arrays_rel_from src start heads nexts"
  shows "length nexts = length src"
  using assms by (simp add: source_index_arrays_rel_from_def)

lemma source_positions_from_empty:
  assumes "length src - min_match + 1 \<le> start"
  shows "source_positions_from src start = []"
  using assms
  by (cases "length src < min_match")
     (simp_all add: source_positions_from_def)

lemma source_index_arrays_rel_from_empty:
  assumes heads_len: "length heads = hash_size"
      and nexts_len: "length nexts = length src"
      and heads_empty: "\<And>h. h < hash_size \<Longrightarrow> heads ! h = no_entry32"
      and start_ge: "length src - min_match + 1 \<le> start"
  shows "source_index_arrays_rel_from src start heads nexts"
  unfolding source_index_arrays_rel_from_def
proof (intro conjI allI impI)
  show "length heads = hash_size"
    using heads_len .
  show "length nexts = length src"
    using nexts_len .
  fix h
  assume h_lt: "h < hash_size"
  have "source_index_bucket_from src start h = []"
    using start_ge
    by (simp add: source_index_bucket_from_def source_positions_from_empty)
  then show "let bucket = source_index_bucket_from src start h in
        if bucket = [] then heads ! h = no_entry32
        else heads ! h = word_of_nat (hd bucket) \<and>
             match_word_chain nexts (length bucket) (heads ! h) = bucket"
    using heads_empty[OF h_lt] by simp
qed

lemma source_index_heap_rel_from_empty:
  assumes heads_empty:
        "\<And>h. h < hash_size \<Longrightarrow>
          heap_w32 s (head_arr +\<^sub>p int h) = no_entry32"
      and start_ge: "length src - min_match + 1 \<le> start"
  shows "source_index_heap_rel_from s src start head_arr next_arr"
  unfolding source_index_heap_rel_from_def
  apply (rule source_index_arrays_rel_from_empty)
     apply simp
    apply simp
   apply (simp add: heap_w32_list_nth heads_empty)
  using start_ge
  apply simp
  done

lemma source_positions_from_step:
  assumes src_long: "min_match \<le> length src"
      and i_pos: "0 < i"
      and i_le: "i \<le> length src - min_match + 1"
  shows "source_positions_from src (i - 1) =
         (i - 1) # source_positions_from src i"
proof -
  have i_minus_lt: "i - 1 < length src - min_match + 1"
    using i_pos i_le by simp
  have range_eq:
    "[i - 1..<length src - min_match + 1] =
     (i - 1) # [i..<length src - min_match + 1]"
    using i_pos i_minus_lt
    by (simp add: upt_conv_Cons del: upt_Suc)
  show ?thesis
    using src_long range_eq
    by (simp add: source_positions_from_def)
qed

lemma source_index_bucket_from_step:
  assumes src_long: "min_match \<le> length src"
      and i_pos: "0 < i"
      and i_le: "i \<le> length src - min_match + 1"
  shows "source_index_bucket_from src (i - 1) h =
    (if hash_bucket_spec src (i - 1) = h
     then (i - 1) # source_index_bucket_from src i h
     else source_index_bucket_from src i h)"
  using source_positions_from_step[OF src_long i_pos i_le]
  by (simp add: source_index_bucket_from_def)

lemma source_positions_from_member_bounds:
  assumes p_in: "p \<in> set (source_positions_from src start)"
  shows "start \<le> p \<and> p + min_match \<le> length src"
  using p_in
  by (cases "length src < min_match")
     (auto simp: source_positions_from_def)

lemma source_index_bucket_from_member_bounds:
  assumes p_in: "p \<in> set (source_index_bucket_from src start h)"
  shows "start \<le> p \<and> p + min_match \<le> length src"
  using p_in source_positions_from_member_bounds[of p src start]
  by (auto simp: source_index_bucket_from_def)

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

lemma match_word_chain_update_irrelevant:
  assumes p_notin: "p \<notin> set (match_word_chain nexts fuel cand)"
  shows "match_word_chain (nexts[p := v]) fuel cand =
         match_word_chain nexts fuel cand"
  using p_notin
proof (induction fuel arbitrary: cand)
  case 0
  then show ?case
    by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "cand = no_entry32 \<or> \<not> unat cand < length nexts")
    case True
    then show ?thesis
      by auto
  next
    case False
    then have cand_ok: "cand \<noteq> no_entry32" "unat cand < length nexts"
      by auto
    have p_ne: "p \<noteq> unat cand"
      using Suc.prems cand_ok by auto
    have p_notin_tail:
      "p \<notin> set (match_word_chain nexts fuel (nexts ! unat cand))"
      using Suc.prems cand_ok by auto
    have tail:
      "match_word_chain (nexts[p := v]) fuel (nexts ! unat cand) =
       match_word_chain nexts fuel (nexts ! unat cand)"
      by (rule Suc.IH[OF p_notin_tail])
    show ?thesis
      using cand_ok p_ne tail by simp
  qed
qed

lemma word32_of_nat_no_entry32:
  assumes "p < unat (no_entry32 :: 32 word)"
  shows "(of_nat p :: 32 word) \<noteq> no_entry32"
proof
  assume "(of_nat p :: 32 word) = no_entry32"
  hence "unat (of_nat p :: 32 word) = unat (no_entry32 :: 32 word)"
    by simp
  with assms show False
    by (simp add: unat_of_nat_eq)
qed

lemma match_word_chain_cons_update:
  assumes p_lt: "p < length nexts"
      and p_unat: "unat (of_nat p :: 32 word) = p"
      and p_not_sentinel: "(of_nat p :: 32 word) \<noteq> no_entry32"
      and old_chain: "match_word_chain nexts fuel old_head = bucket"
      and p_notin: "p \<notin> set bucket"
  shows "match_word_chain (nexts[p := old_head]) (Suc fuel) (of_nat p) =
         p # bucket"
proof -
  have updated_tail:
    "match_word_chain (nexts[p := old_head]) fuel old_head =
     match_word_chain nexts fuel old_head"
    using old_chain p_notin
    by (intro match_word_chain_update_irrelevant) simp
  show ?thesis
    using p_lt p_unat p_not_sentinel old_chain updated_tail
    by simp
qed

lemma source_index_arrays_rel_from_step:
  assumes rel: "source_index_arrays_rel_from src i heads nexts"
      and src_long: "min_match \<le> length src"
      and i_pos: "0 < i"
      and i_le: "i \<le> length src - min_match + 1"
      and src_len_word: "length src < unat (no_entry32 :: 32 word)"
  defines "p \<equiv> i - 1"
  defines "bucket \<equiv> hash_bucket_spec src p"
  shows "source_index_arrays_rel_from src p
    (heads[bucket := of_nat p]) (nexts[p := heads ! bucket])"
proof -
  have heads_len: "length heads = hash_size"
    using rel by (simp add: source_index_arrays_rel_from_def)
  have nexts_len: "length nexts = length src"
    using rel by (simp add: source_index_arrays_rel_from_def)
  have p_lt_src: "p < length src"
    using src_long i_pos i_le
    by (simp add: p_def min_match_def)
  have p_lt_nexts: "p < length nexts"
    using p_lt_src nexts_len by simp
  have p_unat: "unat (of_nat p :: 32 word) = p"
    using p_lt_src src_len_word
    by (simp add: unat_of_nat_eq)
  have p_not_sentinel: "(of_nat p :: 32 word) \<noteq> no_entry32"
    using p_lt_src src_len_word
    by (intro word32_of_nat_no_entry32) simp
  have bucket_lt: "bucket < hash_size"
    by (simp add: bucket_def)
  show ?thesis
    unfolding source_index_arrays_rel_from_def
  proof (intro conjI allI impI)
    show "length (heads[bucket := of_nat p]) = hash_size"
      using heads_len by simp
    show "length (nexts[p := heads ! bucket]) = length src"
      using nexts_len by simp
    fix h
    assume h_lt: "h < hash_size"
    let ?old = "source_index_bucket_from src i h"
    let ?new = "source_index_bucket_from src p h"
    let ?heads' = "heads[bucket := of_nat p]"
    let ?nexts' = "nexts[p := heads ! bucket]"
    have bucket_step:
      "?new = (if bucket = h then p # ?old else ?old)"
      using source_index_bucket_from_step[OF src_long i_pos i_le, of h]
      by (simp add: p_def bucket_def)
    have rel_h:
      "let bucket = ?old in
        if bucket = [] then heads ! h = no_entry32
        else heads ! h = word_of_nat (hd bucket) \<and>
             match_word_chain nexts (length bucket) (heads ! h) = bucket"
      using rel h_lt
      unfolding source_index_arrays_rel_from_def by blast
    have p_notin_old: "p \<notin> set ?old"
    proof
      assume p_in: "p \<in> set ?old"
      have "i \<le> p"
        using source_index_bucket_from_member_bounds[OF p_in] by simp
      with i_pos show False
        by (simp add: p_def)
    qed
    show "let bucket = ?new in
        if bucket = [] then ?heads' ! h = no_entry32
        else ?heads' ! h = word_of_nat (hd bucket) \<and>
             match_word_chain ?nexts' (length bucket) (?heads' ! h) = bucket"
    proof (cases "bucket = h")
      case True
      have head_new: "?heads' ! h = of_nat p"
        using True bucket_lt heads_len by simp
      have old_chain:
        "match_word_chain nexts (length ?old) (heads ! h) = ?old"
      proof (cases "?old = []")
        case True
        then show ?thesis by simp
      next
        case False
        have rel_unlet:
          "if ?old = [] then heads ! h = no_entry32
           else heads ! h = of_nat (hd ?old) \<and>
                match_word_chain nexts (length ?old) (heads ! h) = ?old"
          using rel_h unfolding Let_def .
        from rel_unlet False have conj:
          "heads ! h = of_nat (hd ?old) \<and>
           match_word_chain nexts (length ?old) (heads ! h) = ?old"
          apply (subst (asm) if_not_P)
           apply assumption
          apply assumption
          done
        show ?thesis
          by (rule conjunct2[OF conj])
      qed
      have chain_new:
        "match_word_chain ?nexts' (length ?new) (?heads' ! h) = ?new"
        using match_word_chain_cons_update[
            OF p_lt_nexts p_unat p_not_sentinel old_chain p_notin_old]
          bucket_step True head_new
        by simp
      show ?thesis
        using bucket_step True head_new chain_new by simp
    next
      case False
      have head_same: "?heads' ! h = heads ! h"
        using False by simp
      have bucket_same: "?new = ?old"
        using bucket_step False by simp
      show ?thesis
      proof (cases "?old = []")
        case True
        with rel_h head_same bucket_same show ?thesis
          by (simp add: Let_def)
      next
        case old_nonempty: False
        have rel_unlet:
          "if ?old = [] then heads ! h = no_entry32
           else heads ! h = of_nat (hd ?old) \<and>
                match_word_chain nexts (length ?old) (heads ! h) = ?old"
          using rel_h unfolding Let_def .
        from rel_unlet old_nonempty have old_conj:
          "heads ! h = of_nat (hd ?old) \<and>
           match_word_chain nexts (length ?old) (heads ! h) = ?old"
          apply (subst (asm) if_not_P)
           apply assumption
          apply assumption
          done
        have old_head:
          "heads ! h = of_nat (hd ?old)"
          by (rule conjunct1[OF old_conj])
        have old_chain:
          "match_word_chain nexts (length ?old) (heads ! h) = ?old"
          by (rule conjunct2[OF old_conj])
        have chain_same:
          "match_word_chain ?nexts' (length ?old) (heads ! h) = ?old"
        proof -
          have "p \<notin> set (match_word_chain nexts (length ?old) (heads ! h))"
            using old_chain p_notin_old by simp
          hence "match_word_chain ?nexts' (length ?old) (heads ! h) =
                 match_word_chain nexts (length ?old) (heads ! h)"
            by (rule match_word_chain_update_irrelevant)
          with old_chain show ?thesis by simp
        qed
        show ?thesis
          using bucket_same head_same old_head chain_same old_nonempty by simp
      qed
    qed
  qed
qed

lemma source_index_heap_rel_from_step:
  fixes head_arr next_arr :: "32 word ptr"
  assumes rel:
      "source_index_heap_rel_from s src i head_arr next_arr"
    and src_long: "min_match \<le> length src"
    and i_pos: "0 < i"
    and i_le: "i \<le> length src - min_match + 1"
    and src_len_word: "length src < unat (no_entry32 :: 32 word)"
    and head_no_alias:
      "\<And>h. h < hash_size \<Longrightarrow> h \<noteq> bucket \<Longrightarrow>
        head_arr +\<^sub>p int h \<noteq> head_arr +\<^sub>p int bucket"
    and next_no_alias:
      "\<And>q. q < length src \<Longrightarrow> q \<noteq> p \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
    and next_head_disjoint:
      "\<And>h. h < hash_size \<Longrightarrow>
        head_arr +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
    and head_next_disjoint:
      "\<And>q. q < length src \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> head_arr +\<^sub>p int bucket"
    and p_def: "p = i - 1"
    and bucket_def: "bucket = hash_bucket_spec src p"
  defines "s_next \<equiv>
    heap_w32_update
      (\<lambda>a. a(next_arr +\<^sub>p int p :=
        heap_w32 s (head_arr +\<^sub>p int bucket))) s"
  defines "s_head \<equiv>
    heap_w32_update
      (\<lambda>ha. ha(head_arr +\<^sub>p int bucket := of_nat p)) s_next"
  shows "source_index_heap_rel_from s_head src p head_arr next_arr"
proof -
  let ?heads = "heap_w32_list s head_arr hash_size"
  let ?nexts = "heap_w32_list s next_arr (length src)"
  have arrays_rel:
    "source_index_arrays_rel_from src i ?heads ?nexts"
    using rel by (simp add: source_index_heap_rel_from_def)
  have p_lt_src: "p < length src"
    using src_long i_pos i_le
    by (simp add: p_def min_match_def)
  have bucket_lt: "bucket < hash_size"
    by (simp add: bucket_def)
  have head_value:
    "heap_w32 s (head_arr +\<^sub>p int bucket) = ?heads ! bucket"
    using bucket_lt by simp
  have heads_after_next:
    "heap_w32_list s_next head_arr hash_size = ?heads"
    unfolding s_next_def
    apply (rule heap_w32_list_update_outside)
    using next_head_disjoint
    by auto
  have nexts_after_next:
    "heap_w32_list s_next next_arr (length src) =
     ?nexts[p := ?heads ! bucket]"
    unfolding s_next_def
    apply (subst head_value)
    apply (rule heap_w32_list_update_index)
      apply (rule p_lt_src)
     apply simp
    using next_no_alias
    apply auto
    done
  have heads_after_head:
    "heap_w32_list s_head head_arr hash_size =
     ?heads[bucket := of_nat p]"
    unfolding s_head_def
    apply (subst heads_after_next[symmetric])
    apply (rule heap_w32_list_update_index)
      apply (rule bucket_lt)
     apply simp
    using head_no_alias
    apply auto
    done
  have nexts_after_head:
    "heap_w32_list s_head next_arr (length src) =
     ?nexts[p := ?heads ! bucket]"
    unfolding s_head_def
    apply (subst nexts_after_next[symmetric])
    apply (rule heap_w32_list_update_outside)
    using head_next_disjoint
    by auto
  have arrays_after:
    "source_index_arrays_rel_from src p
      (?heads[bucket := of_nat p]) (?nexts[p := ?heads ! bucket])"
  proof -
    have "source_index_arrays_rel_from src (i - 1)
      (?heads[hash_bucket_spec src (i - 1) := of_nat (i - 1)])
      (?nexts[i - 1 := ?heads ! hash_bucket_spec src (i - 1)])"
      by (rule source_index_arrays_rel_from_step[
          OF arrays_rel src_long i_pos i_le src_len_word])
    then show ?thesis
      by (simp add: p_def bucket_def)
  qed
  show ?thesis
    using arrays_after heads_after_head nexts_after_head
    by (simp add: source_index_heap_rel_from_def)
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

lemma source_index_heap_rel_take_bucket_chain:
  assumes rel: "source_index_heap_rel s src head_arr next_arr"
      and h_lt: "h < hash_size"
  shows "match_word_chain (heap_w32_list s next_arr (length src))
           (min n (length (index_bucket_spec (build_index_spec src) h)))
           (heap_w32 s (head_arr +\<^sub>p int h)) =
         take n (index_bucket_spec (build_index_spec src) h)"
proof -
  have arrays:
    "source_index_arrays_rel src
      (heap_w32_list s head_arr hash_size)
      (heap_w32_list s next_arr (length src))"
    using rel by (simp add: source_index_heap_rel_def)
  have chain:
    "match_word_chain (heap_w32_list s next_arr (length src))
       (min n (length (index_bucket_spec (build_index_spec src) h)))
       (heap_w32_list s head_arr hash_size ! h) =
     take n (index_bucket_spec (build_index_spec src) h)"
    by (rule source_index_arrays_rel_take_bucket_chain[OF arrays h_lt])
  thus ?thesis
    using h_lt by simp
qed

lemma source_index_heap_rel_take_chain_member_sound:
  assumes rel: "source_index_heap_rel s src head_arr next_arr"
      and h_lt: "h < hash_size"
      and p_in: "p \<in> set (match_word_chain
        (heap_w32_list s next_arr (length src))
        (min n (length (index_bucket_spec (build_index_spec src) h)))
        (heap_w32 s (head_arr +\<^sub>p int h)))"
  shows "p + min_match \<le> length src \<and> hash_bucket_spec src p = h"
proof -
  have chain:
    "match_word_chain (heap_w32_list s next_arr (length src))
       (min n (length (index_bucket_spec (build_index_spec src) h)))
       (heap_w32 s (head_arr +\<^sub>p int h)) =
     take n (index_bucket_spec (build_index_spec src) h)"
    by (rule source_index_heap_rel_take_bucket_chain[OF rel h_lt])
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

lemma hash_mask_0xFFFF_32:
  "(0xFFFF :: 32 word) = mask hash_bits"
  by (simp add: hash_bits_def mask_eq_exp_minus_1)

lemma word32_hash_mask_of_nat:
  "((of_nat n :: 32 word) && 0xFFFF) =
   (of_nat (n mod hash_size) :: 32 word)"
proof -
  have "((of_nat n :: 32 word) mod (2 ^ hash_bits)) =
        ((of_nat n :: 32 word) && mask hash_bits)"
    by (rule word_mod_2p_is_mask) (simp_all add: hash_bits_def)
  moreover have "((of_nat n :: 32 word) mod (2 ^ hash_bits)) =
        (of_nat (n mod hash_size) :: 32 word)"
    by (simp add: word_arith_nat_mod unat_of_nat hash_size_def
        hash_bits_def mod_mod_cancel)
  ultimately show ?thesis
    by (simp add: hash_mask_0xFFFF_32)
qed

lemma hash_bucket_word_from_hash4_spec:
  "((of_nat (hash4_spec bs p) :: 32 word) && 0xFFFF) =
   (of_nat (hash_bucket_spec bs p) :: 32 word)"
  by (simp add: word32_hash_mask_of_nat hash_bucket_spec_def)

definition build_index_hashes_ok ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow> byte list \<Rightarrow> bool" where
  "build_index_hashes_ok s0 src src_len src_bytes \<longleftrightarrow>
     (\<forall>p st. heap_typing st = heap_typing s0 \<longrightarrow>
       heap_bytes st src (unat src_len) = src_bytes \<longrightarrow>
       unat p + min_match \<le> length src_bytes \<longrightarrow>
       hash4' src p st =
         Some (of_nat (hash4_spec src_bytes (unat p)) :: 32 word))"

lemma word32_or_disjoint_unat:
  fixes x y :: "32 word"
  assumes disjoint: "x AND y = 0"
      and no_overflow: "unat x + unat y < 2 ^ 32"
  shows "unat (x OR y) = unat x + unat y"
proof -
  have sum_eq: "x + y = x OR y"
    using disjoint by (metis add.left_neutral word_plus_and_or)
  have "unat (x + y) = unat x + unat y"
    using no_overflow by (simp add: unat_plus_if_size word_size)
  thus ?thesis
    using sum_eq by simp
qed

lemma hash4_pack_word:
  fixes b0 b1 b2 b3 :: "8 word"
  shows "(((ucast b0 :: 32 word) ||
            (ucast b1 << 8)) ||
           (ucast b2 << 16) ||
           (ucast b3 << 24)) =
         (of_nat (unat b0 + 256 * unat b1 +
           65536 * unat b2 + 16777216 * unat b3) :: 32 word)"
proof -
  let ?w0 = "(ucast b0 :: 32 word)"
  let ?w1 = "(ucast b1 :: 32 word) << 8"
  let ?w2 = "(ucast b2 :: 32 word) << 16"
  let ?w3 = "(ucast b3 :: 32 word) << 24"
  let ?sum = "unat b0 + 256 * unat b1 +
    65536 * unat b2 + 16777216 * unat b3"

  have b0_le: "unat b0 \<le> 255"
    using unat_lt2p[of b0] by simp
  have b1_le: "unat b1 \<le> 255"
    using unat_lt2p[of b1] by simp
  have b2_le: "unat b2 \<le> 255"
    using unat_lt2p[of b2] by simp
  have b3_le: "unat b3 \<le> 255"
    using unat_lt2p[of b3] by simp
  have sum_bound: "?sum < 2 ^ 32"
  proof -
    have "?sum \<le> 4294967295"
      using b0_le b1_le b2_le b3_le by linarith
    thus ?thesis
      by simp
  qed

  have u0: "unat ?w0 = unat b0"
    by (simp add: unat_ucast_upcast is_up)
  have u1: "unat ?w1 = 256 * unat b1"
  proof -
    have step: "unat ?w1 = unat b1 * 256 mod 4294967296"
      by (simp add: shiftl_t2n unat_word_ariths(2)
          unat_ucast_upcast is_up mult.commute)
    have "unat b1 * 256 < 4294967296"
      using b1_le by linarith
    thus ?thesis
      using step by (simp add: mult.commute)
  qed
  have u2: "unat ?w2 = 65536 * unat b2"
  proof -
    have step: "unat ?w2 = unat b2 * 65536 mod 4294967296"
      by (simp add: shiftl_t2n unat_word_ariths(2)
          unat_ucast_upcast is_up mult.commute)
    have "unat b2 * 65536 < 4294967296"
      using b2_le by linarith
    thus ?thesis
      using step by (simp add: mult.commute)
  qed
  have u3: "unat ?w3 = 16777216 * unat b3"
  proof -
    have step: "unat ?w3 = unat b3 * 16777216 mod 4294967296"
      by (simp add: shiftl_t2n unat_word_ariths(2)
          unat_ucast_upcast is_up mult.commute)
    have "unat b3 * 16777216 < 4294967296"
      using b3_le by linarith
    thus ?thesis
      using step by (simp add: mult.commute)
  qed

  have dis01: "?w0 AND ?w1 = 0"
    by (intro word_eqI) (auto simp: bit_simps word_size dest: bit_imp_le_length)
  have no01: "unat ?w0 + unat ?w1 < 2 ^ 32"
  proof -
    have "unat ?w0 + unat ?w1 \<le> 65535"
      using u0 u1 b0_le b1_le by linarith
    thus ?thesis
      by simp
  qed
  have u01: "unat (?w0 OR ?w1) = unat b0 + 256 * unat b1"
    using word32_or_disjoint_unat[OF dis01 no01] u0 u1 by simp

  have dis012: "(?w0 OR ?w1) AND ?w2 = 0"
    by (intro word_eqI) (auto simp: bit_simps word_size dest: bit_imp_le_length)
  have no012: "unat (?w0 OR ?w1) + unat ?w2 < 2 ^ 32"
  proof -
    have "unat (?w0 OR ?w1) + unat ?w2 \<le> 16777215"
      using u01 u2 b0_le b1_le b2_le by linarith
    thus ?thesis
      by simp
  qed
  have u012:
    "unat ((?w0 OR ?w1) OR ?w2) =
      unat b0 + 256 * unat b1 + 65536 * unat b2"
    using word32_or_disjoint_unat[OF dis012 no012] u01 u2 by simp

  have dis0123: "((?w0 OR ?w1) OR ?w2) AND ?w3 = 0"
    by (intro word_eqI) (auto simp: bit_simps word_size dest: bit_imp_le_length)
  have no0123: "unat ((?w0 OR ?w1) OR ?w2) + unat ?w3 < 2 ^ 32"
    using u012 u3 sum_bound by simp
  have u0123: "unat (((?w0 OR ?w1) OR ?w2) OR ?w3) = ?sum"
    using word32_or_disjoint_unat[OF dis0123 no0123] u012 u3 by simp

  have "(((?w0 OR ?w1) OR ?w2) OR ?w3) =
      (of_nat (unat (((?w0 OR ?w1) OR ?w2) OR ?w3)) :: 32 word)"
    by simp
  also have "\<dots> = (of_nat ?sum :: 32 word)"
    using u0123 by simp
  finally have left_assoc:
    "(((?w0 OR ?w1) OR ?w2) OR ?w3) = (of_nat ?sum :: 32 word)" .
  thus ?thesis
    by (simp add: word_bw_assocs)
qed

lemma hash4_pack_mul_word:
  fixes n0 n1 n2 n3 :: nat
  shows "((of_nat (n0 + 256 * n1 + 65536 * n2 + 16777216 * n3) :: 32 word) *
          0x9E3779B1) =
         (of_nat (((n0 + 256 * n1 + 65536 * n2 + 16777216 * n3) *
           2654435761) mod 4294967296) :: 32 word)"
proof -
  let ?a = "n0 + 256 * n1 + 65536 * n2 + 16777216 * n3"
  have mod_word:
    "(of_nat ((?a * 2654435761) mod 4294967296) :: 32 word) =
     of_nat (?a * 2654435761)"
  proof (rule word_of_nat_eq_iff[THEN iffD2])
    show "take_bit LENGTH(32) ((?a * 2654435761) mod 4294967296) =
      take_bit LENGTH(32) (?a * 2654435761)"
      by (simp add: take_bit_eq_mod)
  qed
  have "((of_nat ?a :: 32 word) * 0x9E3779B1) =
      (of_nat (?a * 2654435761) :: 32 word)"
    by simp
  also have "\<dots> = (of_nat ((?a * 2654435761) mod 4294967296) :: 32 word)"
    using mod_word by simp
  finally show ?thesis .
qed

lemma hash4'_heap_bytes:
  fixes src :: "8 word ptr"
    and p :: "32 word"
  assumes bytes: "heap_bytes st src n = src_bytes"
      and len: "unat p + min_match \<le> length src_bytes"
      and src_bytes_len: "length src_bytes < 2 ^ 32"
      and valid:
        "\<And>k. k < min_match \<Longrightarrow>
          IS_VALID(8 word) st (src +\<^sub>p uint (p + of_nat k :: 32 word))"
  shows "hash4' src p st =
    Some (of_nat (hash4_spec src_bytes (unat p)) :: 32 word)"
proof -
  have k_unat:
    "\<And>k. k < min_match \<Longrightarrow>
      unat (p + of_nat k :: 32 word) = unat p + k"
  proof -
    fix k
    assume k_lt: "k < min_match"
    have no_overflow: "unat p + unat (4 :: 32 word) < 2 ^ 32"
      using len src_bytes_len by (simp add: min_match_def)
    show "unat (p + of_nat k :: 32 word) = unat p + k"
      by (rule unat_add_of_nat_index[where sz = "4", OF _ no_overflow])
         (use k_lt in \<open>simp add: min_match_def\<close>)
  qed
  have idx_lt:
    "\<And>k. k < min_match \<Longrightarrow> unat p + k < length src_bytes"
    using len by (simp add: min_match_def)
  have byte_eq:
    "\<And>k. k < min_match \<Longrightarrow>
      heap_w8 st (src +\<^sub>p uint (p + of_nat k :: 32 word)) =
      src_bytes ! (unat p + k)"
  proof -
    fix k
    assume k_lt: "k < min_match"
    have n_eq: "n = length src_bytes"
    proof -
      have "length (heap_bytes st src n) = length src_bytes"
        using bytes by simp
      thus ?thesis
        by simp
    qed
    have idx: "unat (p + of_nat k :: 32 word) = unat p + k"
      by (rule k_unat[OF k_lt])
    have "src_bytes ! (unat p + k) =
      heap_w8 st (src +\<^sub>p int (unat p + k))"
      using heap_bytes_nth[of "unat p + k" n st src] idx_lt[OF k_lt] bytes n_eq
      by simp
    thus "heap_w8 st (src +\<^sub>p uint (p + of_nat k :: 32 word)) =
      src_bytes ! (unat p + k)"
      by (simp only: idx[symmetric] uint_nat)
  qed
  have valid0: "IS_VALID(8 word) st (src +\<^sub>p uint p)"
    using valid[of 0] by (simp add: min_match_def)
  have valid1: "IS_VALID(8 word) st (src +\<^sub>p uint (p + 1))"
    using valid[of 1] by (simp add: min_match_def)
  have valid2: "IS_VALID(8 word) st (src +\<^sub>p uint (p + 2))"
    using valid[of 2] by (simp add: min_match_def)
  have valid3: "IS_VALID(8 word) st (src +\<^sub>p uint (p + 3))"
    using valid[of 3] by (simp add: min_match_def)
  have byte0:
    "heap_w8 st (src +\<^sub>p uint p) = src_bytes ! unat p"
    using byte_eq[of 0] by (simp add: min_match_def)
  have byte1:
    "heap_w8 st (src +\<^sub>p uint (p + 1)) = src_bytes ! Suc (unat p)"
    using byte_eq[of 1] by (simp add: min_match_def)
  have byte2:
    "heap_w8 st (src +\<^sub>p uint (p + 2)) = src_bytes ! Suc (Suc (unat p))"
    using byte_eq[of 2] by (simp add: min_match_def)
  have byte3:
    "heap_w8 st (src +\<^sub>p uint (p + 3)) = src_bytes ! (unat p + 3)"
    using byte_eq[of 3] by (simp add: min_match_def)
  let ?b0 = "src_bytes ! unat p"
  let ?b1 = "src_bytes ! Suc (unat p)"
  let ?b2 = "src_bytes ! Suc (Suc (unat p))"
  let ?b3 = "src_bytes ! (unat p + 3)"
  let ?packed = "unat ?b0 + 256 * unat ?b1 +
    65536 * unat ?b2 + 16777216 * unat ?b3"
  have spec_eq:
    "hash4_spec src_bytes (unat p) =
      (?packed * 2654435761) mod 4294967296"
    unfolding hash4_spec_def by simp
  have pack_eq:
    "((((ucast ?b0 :: 32 word) ||
        (ucast ?b1 << 8)) ||
       (ucast ?b2 << 16)) ||
      (ucast ?b3 << 24)) =
     (of_nat ?packed :: 32 word)"
    using hash4_pack_word[of ?b0 ?b1 ?b2 ?b3]
    by (simp only: word_bw_assocs)
  have mul_eq:
    "((of_nat ?packed :: 32 word) * 0x9E3779B1) =
     (of_nat ((?packed * 2654435761) mod 4294967296) :: 32 word)"
    by (rule hash4_pack_mul_word)
  have hash_eq:
    "((((ucast (src_bytes ! unat p) :: 32 word) ||
        (ucast (src_bytes ! Suc (unat p)) << 8)) ||
       (ucast (src_bytes ! Suc (Suc (unat p))) << 16)) ||
      (ucast (src_bytes ! (unat p + 3)) << 24)) *
     0x9E3779B1 =
     (of_nat (hash4_spec src_bytes (unat p)) :: 32 word)"
  proof -
    have "((((ucast ?b0 :: 32 word) ||
        (ucast ?b1 << 8)) ||
       (ucast ?b2 << 16)) ||
      (ucast ?b3 << 24)) *
      0x9E3779B1 =
      (of_nat ?packed :: 32 word) * 0x9E3779B1"
      using pack_eq by simp
    also have "\<dots> =
      (of_nat ((?packed * 2654435761) mod 4294967296) :: 32 word)"
      by (rule mul_eq)
    also have "\<dots> =
      (of_nat (hash4_spec src_bytes (unat p)) :: 32 word)"
      using spec_eq by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding hash4'_def
    apply (simp add: obind_def oguard_def ogets_def
        valid0 valid1 valid2 valid3 byte0 byte1 byte2 byte3 min_match_def
        hash_eq)
    done
qed

lemma build_index_hashes_okI:
  fixes src :: "8 word ptr"
  assumes src_valid:
    "\<And>(off :: 32 word) (st' :: lifted_globals).
      \<lbrakk>heap_typing st' = heap_typing s0; unat off < unat src_len\<rbrakk> \<Longrightarrow>
      IS_VALID(8 word) st' (src +\<^sub>p uint off)"
  shows "build_index_hashes_ok s0 src src_len
    (heap_bytes s0 src (unat src_len))"
  unfolding build_index_hashes_ok_def
proof (intro allI impI)
  fix p :: "32 word"
  fix st :: lifted_globals
  assume typing: "heap_typing st = heap_typing s0"
  assume bytes:
    "heap_bytes st src (unat src_len) = heap_bytes s0 src (unat src_len)"
  assume len:
    "unat p + min_match \<le> length (heap_bytes s0 src (unat src_len))"
  have src_bytes_len:
    "length (heap_bytes s0 src (unat src_len)) < 2 ^ 32"
    using unat_lt2p[of src_len] by simp
  have valid:
    "\<And>k. k < min_match \<Longrightarrow>
      IS_VALID(8 word) st (src +\<^sub>p uint (p + of_nat k :: 32 word))"
  proof -
    fix k
    assume k_lt: "k < min_match"
    have no_overflow: "unat p + unat (4 :: 32 word) < 2 ^ 32"
      using len src_bytes_len by (simp add: min_match_def)
    have k_unat:
      "unat (p + of_nat k :: 32 word) = unat p + k"
      by (rule unat_add_of_nat_index[where sz = "4", OF _ no_overflow])
         (use k_lt in \<open>simp add: min_match_def\<close>)
    have off_lt: "unat (p + of_nat k :: 32 word) < unat src_len"
      using len k_lt k_unat by (simp add: min_match_def)
    show "IS_VALID(8 word) st
      (src +\<^sub>p uint (p + of_nat k :: 32 word))"
      by (rule src_valid[
          where st' = st and off = "(p + of_nat k :: 32 word)",
          OF typing off_lt])
  qed
  show "hash4' src p st =
    Some (of_nat
      (hash4_spec (heap_bytes s0 src (unat src_len)) (unat p)) :: 32 word)"
    by (rule hash4'_heap_bytes[OF bytes len src_bytes_len valid])
qed

definition build_index_fill_inv ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow> byte list \<Rightarrow>
    32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow> 32 word \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "build_index_fill_inv s0 src src_len src_bytes head_arr next_arr i st \<longleftrightarrow>
     heap_typing st = heap_typing s0 \<and>
     heap_bytes st src (unat src_len) = src_bytes \<and>
     length src_bytes = unat src_len \<and>
     min_match \<le> length src_bytes \<and>
     length src_bytes < unat (no_entry32 :: 32 word) \<and>
     unat i \<le> length src_bytes - min_match + 1 \<and>
     source_index_heap_rel_from st src_bytes (unat i) head_arr next_arr"

lemma build_index_fill_body_preserves_inv:
  fixes src :: "8 word ptr"
    and src_len i :: "32 word"
    and head next_arr :: "32 word ptr"
  assumes inv:
      "build_index_fill_inv s0 src src_len src_bytes head next_arr i st"
    and cond: "0 < i"
    and hashes: "build_index_hashes_ok s0 src src_len src_bytes"
    and head_valid:
      "\<And>h (st' :: lifted_globals).
        \<lbrakk>heap_typing st' = heap_typing s0; h < hash_size\<rbrakk> \<Longrightarrow>
        IS_VALID(32 word) st' (head +\<^sub>p int h)"
    and next_valid:
      "\<And>p (st' :: lifted_globals).
        \<lbrakk>heap_typing st' = heap_typing s0; p < length src_bytes\<rbrakk> \<Longrightarrow>
        IS_VALID(32 word) st' (next_arr +\<^sub>p int p)"
    and head_no_alias:
      "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
        head +\<^sub>p int h \<noteq> head +\<^sub>p int bucket"
    and next_no_alias:
      "\<And>q p. \<lbrakk>q < length src_bytes; p < length src_bytes; q \<noteq> p\<rbrakk> \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
    and next_head_disjoint:
      "\<And>h p. \<lbrakk>h < hash_size; p < length src_bytes\<rbrakk> \<Longrightarrow>
        head +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
    and head_next_disjoint:
      "\<And>q bucket. \<lbrakk>q < length src_bytes; bucket < hash_size\<rbrakk> \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int bucket"
  shows "(do {
        p <- return (i - 1);
        hv <- gets_the (hash4' src p);
        h <- return (hv && 0xFFFF);
        guard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint p));
        guard (\<lambda>s. IS_VALID(32 word) s (head +\<^sub>p uint h));
        modify
          (heap_w32_update
            (\<lambda>a. a(next_arr +\<^sub>p uint p := a (head +\<^sub>p uint h))));
        modify (heap_w32_update (\<lambda>ha. ha(head +\<^sub>p uint h := p)));
        return (i - 1)
      } :: (32 word, lifted_globals) res_monad) \<bullet> st
    \<lbrace>\<lambda>r t. r = Result (i - 1) \<and>
      build_index_fill_inv s0 src src_len src_bytes head next_arr (i - 1) t\<rbrace>"
proof -
  let ?p_word = "i - 1"
  let ?p = "unat ?p_word"
  let ?hash = "hash4_spec src_bytes ?p"
  let ?bucket = "hash_bucket_spec src_bytes ?p"
  let ?h = "(of_nat ?bucket :: 32 word)"
  have typing: "heap_typing st = heap_typing s0"
    using inv by (simp add: build_index_fill_inv_def)
  have bytes: "heap_bytes st src (unat src_len) = src_bytes"
    using inv by (simp add: build_index_fill_inv_def)
  have len_src: "length src_bytes = unat src_len"
    using inv by (simp add: build_index_fill_inv_def)
  have src_long: "min_match \<le> length src_bytes"
    using inv by (simp add: build_index_fill_inv_def)
  have src_len_word: "length src_bytes < unat (no_entry32 :: 32 word)"
    using inv by (simp add: build_index_fill_inv_def)
  have i_le: "unat i \<le> length src_bytes - min_match + 1"
    using inv unfolding build_index_fill_inv_def by blast
  have rel: "source_index_heap_rel_from st src_bytes (unat i) head next_arr"
    using inv by (simp add: build_index_fill_inv_def)
  have i_ne: "i \<noteq> 0"
    using cond by (simp add: word_gt_0)
  have i_pos_nat: "0 < unat i"
    using i_ne by (simp add: unat_gt_0)
  have p_unat: "?p = unat i - 1"
    using i_ne by (simp add: unat_minus_one)
  have p_match_bound: "?p + min_match \<le> length src_bytes"
    using i_le i_pos_nat src_long
    by (simp add: p_unat)
  have p_lt_src: "?p < length src_bytes"
    using p_match_bound by (simp add: min_match_def)
  have p_le: "?p \<le> length src_bytes - min_match + 1"
    using i_le by (simp add: p_unat)
  have hash_res:
    "hash4' src ?p_word st = Some (of_nat ?hash :: 32 word)"
    using hashes typing bytes p_match_bound
    by (auto simp: build_index_hashes_ok_def)
  have h_eq[simp]: "(of_nat ?hash :: 32 word) && 0xFFFF = ?h"
    by (rule hash_bucket_word_from_hash4_spec)
  have bucket_lt: "?bucket < hash_size"
    by (rule hash_bucket_spec_lt)
  have bucket_unat: "unat ?h = ?bucket"
    using bucket_lt
    by (simp add: unat_of_nat_eq hash_size_def hash_bits_def)
  have p_word_of_nat[simp]: "(of_nat ?p :: 32 word) = ?p_word"
    by simp
  have p_uint[simp]: "uint ?p_word = int ?p"
    by (simp only: uint_nat)
  have h_uint[simp]: "uint ?h = int ?bucket"
    using bucket_unat by (simp only: uint_nat)
  have next_guard_int:
    "IS_VALID(32 word) st (next_arr +\<^sub>p int ?p)"
    using typing p_lt_src
    by (rule next_valid)
  have next_ptr_eq:
    "next_arr +\<^sub>p uint ?p_word = next_arr +\<^sub>p int ?p"
    by (simp only: p_uint)
  have next_guard:
    "IS_VALID(32 word) st (next_arr +\<^sub>p uint ?p_word)"
    by (subst next_ptr_eq, rule next_guard_int)
  have head_guard_int:
    "IS_VALID(32 word) st (head +\<^sub>p int ?bucket)"
    using typing bucket_lt
    by (rule head_valid)
  have head_ptr_eq:
    "head +\<^sub>p uint ?h = head +\<^sub>p int ?bucket"
    by (simp only: h_uint)
  have head_guard:
    "IS_VALID(32 word) st (head +\<^sub>p uint ?h)"
    by (subst head_ptr_eq, rule head_guard_int)
  let ?s_next =
    "heap_w32_update
      (\<lambda>a. a(next_arr +\<^sub>p int ?p :=
        heap_w32 st (head +\<^sub>p int ?bucket))) st"
  let ?s_head =
    "heap_w32_update
      (\<lambda>ha. ha(head +\<^sub>p int ?bucket := of_nat ?p)) ?s_next"
  have step_rel:
    "source_index_heap_rel_from ?s_head src_bytes ?p head next_arr"
  proof (rule source_index_heap_rel_from_step[
      where i = "unat i" and s = st and p = ?p and bucket = ?bucket])
    show "source_index_heap_rel_from st src_bytes (unat i) head next_arr"
      by (rule rel)
    show "min_match \<le> length src_bytes"
      by (rule src_long)
    show "0 < unat i"
      by (rule i_pos_nat)
    show "unat i \<le> length src_bytes - min_match + 1"
      by (rule i_le)
    show "length src_bytes < unat (no_entry32 :: 32 word)"
      by (rule src_len_word)
    show "\<And>h. h < hash_size \<Longrightarrow> h \<noteq> ?bucket \<Longrightarrow>
        head +\<^sub>p int h \<noteq> head +\<^sub>p int ?bucket"
    proof -
      fix h
      assume h_lt: "h < hash_size"
      assume h_ne: "h \<noteq> ?bucket"
      show "head +\<^sub>p int h \<noteq> head +\<^sub>p int ?bucket"
        by (rule head_no_alias[OF h_lt bucket_lt h_ne])
    qed
    show "\<And>q. q < length src_bytes \<Longrightarrow> q \<noteq> ?p \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int ?p"
    proof -
      fix q
      assume q_lt: "q < length src_bytes"
      assume q_ne: "q \<noteq> ?p"
      show "next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int ?p"
        by (rule next_no_alias[OF q_lt p_lt_src q_ne])
    qed
    show "\<And>h. h < hash_size \<Longrightarrow>
        head +\<^sub>p int h \<noteq> next_arr +\<^sub>p int ?p"
    proof -
      fix h
      assume h_lt: "h < hash_size"
      show "head +\<^sub>p int h \<noteq> next_arr +\<^sub>p int ?p"
        by (rule next_head_disjoint[OF h_lt p_lt_src])
    qed
    show "\<And>q. q < length src_bytes \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int ?bucket"
    proof -
      fix q
      assume q_lt: "q < length src_bytes"
      show "next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int ?bucket"
        by (rule head_next_disjoint[OF q_lt bucket_lt])
    qed
    show "?p = unat i - 1"
      by (rule p_unat)
    show "?bucket = hash_bucket_spec src_bytes ?p"
      by simp
  qed
  have final_state_eq:
    "heap_w32_update
        (\<lambda>ha. ha(head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF) :=
          ?p_word))
        (heap_w32_update
          (\<lambda>a. a(next_arr +\<^sub>p uint ?p_word :=
            a (head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF)))) st) =
     heap_w32_update
        (\<lambda>ha. ha(head +\<^sub>p int ?bucket := of_nat ?p))
        (heap_w32_update
          (\<lambda>a. a(next_arr +\<^sub>p int ?p :=
            heap_w32 st (head +\<^sub>p int ?bucket))) st)"
    apply (subst heap_w32_update_read_current[
      where ptr = "next_arr +\<^sub>p uint ?p_word"
        and src_ptr =
          "head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF)"
        and s = st])
    apply (simp only: h_eq p_uint h_uint p_word_of_nat)
    done
  have step_rel_c:
    "source_index_heap_rel_from
      (heap_w32_update
        (\<lambda>ha. ha(head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF) :=
          ?p_word))
        (heap_w32_update
          (\<lambda>a. a(next_arr +\<^sub>p uint ?p_word :=
            a (head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF)))) st))
      src_bytes (unat ?p_word) head next_arr"
    by (subst final_state_eq, rule step_rel)
  have hash_gets:
    "gets_the (hash4' src ?p_word) \<bullet> st
      \<lbrace>\<lambda>r t. t = st \<and> r = Result (of_nat ?hash :: 32 word)\<rbrace>"
    unfolding gets_the_def
    apply runs_to_vcg
    using hash_res by simp
  have heap_bytes_w32_update[simp]:
    "heap_bytes (heap_w32_update f st') buf n = heap_bytes st' buf n"
    for f st' buf n
    by (simp add: heap_bytes_def)
  let ?st_c =
    "heap_w32_update
      (\<lambda>ha. ha(head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF) :=
        ?p_word))
      (heap_w32_update
        (\<lambda>a. a(next_arr +\<^sub>p uint ?p_word :=
          a (head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF)))) st)"
  have inv_after:
    "build_index_fill_inv s0 src src_len src_bytes head next_arr ?p_word ?st_c"
    unfolding build_index_fill_inv_def
    apply (intro conjI)
          apply (simp only: heap_typing_heap_w32_update typing)
         apply (simp only: heap_bytes_w32_update bytes)
        apply (rule len_src)
       apply (rule src_long)
      apply (rule src_len_word)
     apply (rule p_le)
    apply (rule step_rel_c)
    done
  have inv_after_bucket:
    "build_index_fill_inv s0 src src_len src_bytes head next_arr ?p_word
      (heap_w32_update
        (\<lambda>ha. ha(head +\<^sub>p uint ?h := ?p_word))
        (heap_w32_update
          (\<lambda>a. a(next_arr +\<^sub>p uint ?p_word :=
            a (head +\<^sub>p uint ?h))) st))"
    using inv_after by (simp only: h_eq)
  have body_after_hash_bucket:
    "(do {
        h <- return ?h;
        guard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint ?p_word));
        guard (\<lambda>s. IS_VALID(32 word) s (head +\<^sub>p uint h));
        modify
          (heap_w32_update
            (\<lambda>a. a(next_arr +\<^sub>p uint ?p_word := a (head +\<^sub>p uint h))));
        modify (heap_w32_update (\<lambda>ha. ha(head +\<^sub>p uint h := ?p_word)));
        return ?p_word
      } :: (32 word, lifted_globals) res_monad) \<bullet> st
      \<lbrace>\<lambda>r t. r = Result ?p_word \<and>
        build_index_fill_inv s0 src src_len src_bytes head next_arr ?p_word t\<rbrace>"
    using next_guard head_guard inv_after_bucket
    by (simp only: runs_to.rep_eq run_bind run_guard run_modify
        Spec_Monad.return_bind
        Spec_Monad.bind_post_state_pure_post_state1
        Spec_Monad.holds_pure_post_state
        holds_post_state_run_return
        if_True case_prod_beta fst_conv snd_conv
        Spec_Monad.case_exception_or_result_Result)
  have body_after_hash:
    "(do {
        h <- return ((of_nat ?hash :: 32 word) && 0xFFFF);
        guard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint ?p_word));
        guard (\<lambda>s. IS_VALID(32 word) s (head +\<^sub>p uint h));
        modify
          (heap_w32_update
            (\<lambda>a. a(next_arr +\<^sub>p uint ?p_word := a (head +\<^sub>p uint h))));
        modify (heap_w32_update (\<lambda>ha. ha(head +\<^sub>p uint h := ?p_word)));
        return ?p_word
      } :: (32 word, lifted_globals) res_monad) \<bullet> st
      \<lbrace>\<lambda>r t. r = Result ?p_word \<and>
        build_index_fill_inv s0 src src_len src_bytes head next_arr ?p_word t\<rbrace>"
    apply (simp only: h_eq)
    apply (rule body_after_hash_bucket)
    done
  show ?thesis
    apply runs_to_vcg
    subgoal
      apply (rule exI[where x = "(of_nat ?hash :: 32 word)"])
      apply (intro conjI)
       apply (rule hash_res)
      apply (rule body_after_hash)
      done
    done
qed

lemma build_index_fill_loop_preserves_inv:
  fixes src :: "8 word ptr"
    and src_len start :: "32 word"
    and head next_arr :: "32 word ptr"
  assumes inv0:
      "build_index_fill_inv s0 src src_len src_bytes head next_arr start st"
    and hashes: "build_index_hashes_ok s0 src src_len src_bytes"
    and head_valid:
      "\<And>h (st' :: lifted_globals).
        \<lbrakk>heap_typing st' = heap_typing s0; h < hash_size\<rbrakk> \<Longrightarrow>
        IS_VALID(32 word) st' (head +\<^sub>p int h)"
    and next_valid:
      "\<And>p (st' :: lifted_globals).
        \<lbrakk>heap_typing st' = heap_typing s0; p < length src_bytes\<rbrakk> \<Longrightarrow>
        IS_VALID(32 word) st' (next_arr +\<^sub>p int p)"
    and head_no_alias:
      "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
        head +\<^sub>p int h \<noteq> head +\<^sub>p int bucket"
    and next_no_alias:
      "\<And>q p. \<lbrakk>q < length src_bytes; p < length src_bytes; q \<noteq> p\<rbrakk> \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
    and next_head_disjoint:
      "\<And>h p. \<lbrakk>h < hash_size; p < length src_bytes\<rbrakk> \<Longrightarrow>
        head +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
    and head_next_disjoint:
      "\<And>q bucket. \<lbrakk>q < length src_bytes; bucket < hash_size\<rbrakk> \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int bucket"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. 0 < i)
      (\<lambda>i. do {
        p <- return (i - 1);
        hv <- gets_the (hash4' src p);
        h <- return (hv && 0xFFFF);
        guard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint p));
        guard (\<lambda>s. IS_VALID(32 word) s (head +\<^sub>p uint h));
        modify
          (heap_w32_update
            (\<lambda>a. a(next_arr +\<^sub>p uint p := a (head +\<^sub>p uint h))));
        modify (heap_w32_update (\<lambda>ha. ha(head +\<^sub>p uint h := p)));
        return (i - 1)
      }) start :: (32 word, lifted_globals) res_monad) \<bullet> st
    \<lbrace>\<lambda>r t. r = Result 0 \<and>
      build_index_fill_inv s0 src src_len src_bytes head next_arr 0 t\<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((i :: 32 word), _). unat i)"
      and I = "\<lambda>i st'. build_index_fill_inv s0 src src_len src_bytes
        head next_arr i st'"])
     apply simp
    apply (rule inv0)
   subgoal for i st'
    by (simp add: word_gt_0)
  subgoal premises prems for i st'
  proof -
    have body:
      "(do {
        p <- return (i - 1);
        hv <- gets_the (hash4' src p);
        h <- return (hv && 0xFFFF);
        guard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint p));
        guard (\<lambda>s. IS_VALID(32 word) s (head +\<^sub>p uint h));
        modify
          (heap_w32_update
            (\<lambda>a. a(next_arr +\<^sub>p uint p := a (head +\<^sub>p uint h))));
        modify (heap_w32_update (\<lambda>ha. ha(head +\<^sub>p uint h := p)));
        return (i - 1)
      } :: (32 word, lifted_globals) res_monad) \<bullet> st'
        \<lbrace>\<lambda>r t. r = Result (i - 1) \<and>
          build_index_fill_inv s0 src src_len src_bytes head next_arr
            (i - 1) t\<rbrace>"
      by (rule build_index_fill_body_preserves_inv[
          OF prems(2) prems(1) hashes])
         (auto intro: head_valid next_valid
           dest: head_no_alias next_no_alias next_head_disjoint
             head_next_disjoint,
          metis head_no_alias hash_size_0x10000)
    show ?thesis
      apply (rule runs_to_weaken[OF body])
       apply simp
      using prems(1)
      apply (auto simp: measure_unat)
      done
  qed
  done

lemma build_index_fill_loop_source_index_heap_rel:
  fixes src :: "8 word ptr"
    and src_len start :: "32 word"
    and head next_arr :: "32 word ptr"
  assumes inv0:
      "build_index_fill_inv s0 src src_len src_bytes head next_arr start st"
    and hashes: "build_index_hashes_ok s0 src src_len src_bytes"
    and head_valid:
      "\<And>h (st' :: lifted_globals).
        \<lbrakk>heap_typing st' = heap_typing s0; h < hash_size\<rbrakk> \<Longrightarrow>
        IS_VALID(32 word) st' (head +\<^sub>p int h)"
    and next_valid:
      "\<And>p (st' :: lifted_globals).
        \<lbrakk>heap_typing st' = heap_typing s0; p < length src_bytes\<rbrakk> \<Longrightarrow>
        IS_VALID(32 word) st' (next_arr +\<^sub>p int p)"
    and head_no_alias:
      "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
        head +\<^sub>p int h \<noteq> head +\<^sub>p int bucket"
    and next_no_alias:
      "\<And>q p. \<lbrakk>q < length src_bytes; p < length src_bytes; q \<noteq> p\<rbrakk> \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
    and next_head_disjoint:
      "\<And>h p. \<lbrakk>h < hash_size; p < length src_bytes\<rbrakk> \<Longrightarrow>
        head +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
    and head_next_disjoint:
      "\<And>q bucket. \<lbrakk>q < length src_bytes; bucket < hash_size\<rbrakk> \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int bucket"
  shows "(whileLoop (\<lambda>(i :: 32 word) st. 0 < i)
      (\<lambda>i. do {
        p <- return (i - 1);
        hv <- gets_the (hash4' src p);
        h <- return (hv && 0xFFFF);
        guard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint p));
        guard (\<lambda>s. IS_VALID(32 word) s (head +\<^sub>p uint h));
        modify
          (heap_w32_update
            (\<lambda>a. a(next_arr +\<^sub>p uint p := a (head +\<^sub>p uint h))));
        modify (heap_w32_update (\<lambda>ha. ha(head +\<^sub>p uint h := p)));
        return (i - 1)
      }) start :: (32 word, lifted_globals) res_monad) \<bullet> st
    \<lbrace>\<lambda>r t. r = Result 0 \<and>
      source_index_heap_rel t src_bytes head next_arr \<and>
      heap_typing t = heap_typing s0\<rbrace>"
  apply (rule runs_to_weaken[OF build_index_fill_loop_preserves_inv[
        OF inv0 hashes]])
        apply (auto intro: head_valid next_valid
          dest: head_no_alias next_no_alias next_head_disjoint
            head_next_disjoint
          simp: build_index_fill_inv_def source_index_heap_rel_from_0)
   apply (metis head_no_alias hash_size_0x10000)
  done

lemma build_index_start_unat:
  fixes src_len :: "32 word"
  assumes src_long: "4 \<le> unat src_len"
  shows "unat (0xFFFFFFFD + src_len :: 32 word) =
         unat src_len - min_match + 1"
proof -
  have three_le: "(3 :: 32 word) \<le> src_len"
    using src_long by (simp add: word_le_nat_alt)
  have start_eq: "(0xFFFFFFFD + src_len :: 32 word) = src_len - 3"
    by simp
  show ?thesis
    using three_le src_long by (simp add: start_eq unat_sub min_match_def)
qed

lemma unat_minus_one_word:
  fixes i :: "32 word"
  assumes i_pos: "0 < i"
  shows "unat (i - 1) = unat i - 1"
proof -
  have one_le: "(1 :: 32 word) \<le> i"
    using i_pos by (simp add: word_le_nat_alt word_less_nat_alt)
  show ?thesis
    using one_le by (simp add: unat_sub)
qed

lemma build_index_head_init_loop:
  fixes head :: "32 word ptr"
    and src :: "8 word ptr"
    and n :: nat
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
          \<and> (\<forall>h < hash_size. heap_w32 t (head +\<^sub>p int h) = no_entry32)
          \<and> heap_bytes t src n = heap_bytes s src n \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((idx :: 32 word), _). hash_size - unat idx)"
      and I = "\<lambda>idx st. unat idx \<le> hash_size
          \<and> heap_typing st = heap_typing s
          \<and> (\<forall>h < unat idx. heap_w32 st (head +\<^sub>p int h) = no_entry32)
          \<and> heap_bytes st src n = heap_bytes s src n"])
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
        using prems(2) by (simp add: heap_bytes_def)
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

lemma build_index'_long_source_index_heap_rel:
  fixes src :: "8 word ptr"
    and src_len :: "32 word"
    and head next_arr :: "32 word ptr"
  assumes src_long_word: "\<not> src_len < (4 :: 32 word)"
      and src_len_word:
        "unat src_len < unat (no_entry32 :: 32 word)"
      and hashes:
        "build_index_hashes_ok s src src_len
          (heap_bytes s src (unat src_len))"
      and head_valid:
        "\<And>h (st' :: lifted_globals).
          \<lbrakk>heap_typing st' = heap_typing s; h < hash_size\<rbrakk> \<Longrightarrow>
          IS_VALID(32 word) st' (head +\<^sub>p int h)"
      and next_valid:
        "\<And>p (st' :: lifted_globals).
          \<lbrakk>heap_typing st' = heap_typing s; p < unat src_len\<rbrakk> \<Longrightarrow>
          IS_VALID(32 word) st' (next_arr +\<^sub>p int p)"
      and head_no_alias:
        "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
          head +\<^sub>p int h \<noteq> head +\<^sub>p int bucket"
      and next_no_alias:
        "\<And>q p. \<lbrakk>q < unat src_len; p < unat src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      and next_head_disjoint:
        "\<And>h p. \<lbrakk>h < hash_size; p < unat src_len\<rbrakk> \<Longrightarrow>
          head +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
      and head_next_disjoint:
        "\<And>q bucket. \<lbrakk>q < unat src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int bucket"
  shows "build_index' src src_len head next_arr \<bullet> s
    \<lbrace> \<lambda>r t. r = Result () \<and>
        source_index_heap_rel t (heap_bytes s src (unat src_len)) head next_arr
        \<and> heap_typing t = heap_typing s \<rbrace>"
proof -
  let ?src_bytes = "heap_bytes s src (unat src_len)"
  let ?start = "(0xFFFFFFFD + src_len :: 32 word)"
  have src_long_nat: "min_match \<le> length ?src_bytes"
    using src_long_word by (simp add: word_less_nat_alt min_match_def)
  have four_le: "4 \<le> unat src_len"
    using src_long_word by (simp add: word_less_nat_alt)
  have start_unat:
    "unat ?start = length ?src_bytes - min_match + 1"
    using build_index_start_unat[OF four_le] by simp
  have len_src_bytes: "length ?src_bytes = unat src_len"
    by simp
  have start_ge:
    "length ?src_bytes - min_match + 1 \<le> unat ?start"
    using start_unat by simp
  have start_le:
    "unat ?start \<le> length ?src_bytes - min_match + 1"
    using start_unat by simp
  have src_len_word_bytes:
    "length ?src_bytes < unat (no_entry32 :: 32 word)"
    using src_len_word by simp
  have head_valid_word:
    "\<And>idx. idx < (0x10000 :: 32 word) \<Longrightarrow>
      IS_VALID(32 word) s (head +\<^sub>p uint idx)"
  proof -
    fix idx :: "32 word"
    assume idx_lt: "idx < (0x10000 :: 32 word)"
    have idx_nat_lt: "unat idx < hash_size"
      using idx_lt by (simp add: word_less_nat_alt)
    have ptr_eq: "head +\<^sub>p uint idx = head +\<^sub>p int (unat idx)"
      by (simp only: uint_nat)
    show "IS_VALID(32 word) s (head +\<^sub>p uint idx)"
      apply (subst ptr_eq)
      by (rule head_valid[where st' = s and h = "unat idx", OF _ idx_nat_lt])
         simp
  qed
  show ?thesis
    unfolding build_index'_def
    apply runs_to_vcg
    subgoal
      apply (rule runs_to_weaken[
        OF build_index_head_init_loop[
          where src = src and n = "unat src_len", OF head_valid_word]])
       apply simp
      subgoal premises prems for r t
      proof -
        have typing_t: "heap_typing t = heap_typing s"
          using prems by simp
        have heads_empty:
          "\<And>h. h < hash_size \<Longrightarrow>
            heap_w32 t (head +\<^sub>p int h) = no_entry32"
          using prems by simp
        have bytes_t: "heap_bytes t src (unat src_len) = ?src_bytes"
          using prems by simp
        have rel_start:
          "source_index_heap_rel_from t ?src_bytes (unat ?start) head next_arr"
        proof (rule source_index_heap_rel_from_empty)
          fix h
          assume h_lt: "h < hash_size"
          show "heap_w32 t (head +\<^sub>p int h) = no_entry32"
            by (rule heads_empty[OF h_lt])
        next
          show "length ?src_bytes - min_match + 1 \<le> unat ?start"
            by (rule start_ge)
        qed
        have init_inv:
          "build_index_fill_inv s src src_len ?src_bytes head next_arr ?start t"
          unfolding build_index_fill_inv_def
          apply (intro conjI)
                apply (rule typing_t)
               apply (rule bytes_t)
              apply (rule len_src_bytes)
             apply (rule src_long_nat)
            apply (rule src_len_word_bytes)
           apply (rule start_le)
          apply (rule rel_start)
          done
        have fill:
          "(whileLoop (\<lambda>(i :: 32 word) st. 0 < i)
            (\<lambda>i. do {
              p <- return (i - 1);
              hv <- gets_the (hash4' src p);
              h <- return (hv && 0xFFFF);
              guard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint p));
              guard (\<lambda>s. IS_VALID(32 word) s (head +\<^sub>p uint h));
              modify
                (heap_w32_update
                  (\<lambda>a. a(next_arr +\<^sub>p uint p := a (head +\<^sub>p uint h))));
              modify (heap_w32_update (\<lambda>ha. ha(head +\<^sub>p uint h := p)));
              return (i - 1)
            }) ?start :: (32 word, lifted_globals) res_monad) \<bullet> t
          \<lbrace>\<lambda>r t. r = Result 0 \<and>
            source_index_heap_rel t ?src_bytes head next_arr \<and>
            heap_typing t = heap_typing s\<rbrace>"
          apply (rule build_index_fill_loop_source_index_heap_rel[
                OF init_inv hashes])
                 apply (auto intro: head_valid next_valid
                   dest: head_no_alias next_no_alias next_head_disjoint
                     head_next_disjoint)
          apply (metis head_no_alias hash_size_0x10000)
          done
        have fill_generated:
          "(whileLoop (\<lambda>(i :: 32 word) st. 0 < i)
            (\<lambda>i. do {
              hv <- gets_the (hash4' src (i - 1));
              guard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint (i - 1)));
              guard (\<lambda>s. IS_VALID(32 word) s (head +\<^sub>p uint (hv && 0xFFFF)));
              modify
                (heap_w32_update
                  (\<lambda>a. a(next_arr +\<^sub>p uint (i - 1) :=
                    a (head +\<^sub>p uint (hv && 0xFFFF)))));
              modify
                (heap_w32_update
                  (\<lambda>h. h(head +\<^sub>p uint (hv && 0xFFFF) := i - 1)));
              return (i - 1)
            }) ?start :: (32 word, lifted_globals) res_monad) \<bullet> t
          \<lbrace>\<lambda>r t. r = Result 0 \<and>
            source_index_heap_rel t ?src_bytes head next_arr \<and>
            heap_typing t = heap_typing s\<rbrace>"
          using fill by (simp only: Spec_Monad.return_bind)
        show ?thesis
          using prems fill src_long_word
          apply (simp add: runs_to_iff split: exception_or_result_splits)
          apply (rule runs_to_weaken[OF fill_generated])
           apply simp
          done
      qed
      done
    done
qed

lemma build_index'_source_index_heap_rel:
  fixes src :: "8 word ptr"
    and src_len :: "32 word"
    and head next_arr :: "32 word ptr"
  assumes src_len_word:
        "unat src_len < unat (no_entry32 :: 32 word)"
      and src_valid:
        "\<And>(off :: 32 word) (st' :: lifted_globals).
          \<lbrakk>heap_typing st' = heap_typing s; unat off < unat src_len\<rbrakk> \<Longrightarrow>
          IS_VALID(8 word) st' (src +\<^sub>p uint off)"
      and head_valid:
        "\<And>h (st' :: lifted_globals).
          \<lbrakk>heap_typing st' = heap_typing s; h < hash_size\<rbrakk> \<Longrightarrow>
          IS_VALID(32 word) st' (head +\<^sub>p int h)"
      and next_valid:
        "\<And>p (st' :: lifted_globals).
          \<lbrakk>heap_typing st' = heap_typing s; p < unat src_len\<rbrakk> \<Longrightarrow>
          IS_VALID(32 word) st' (next_arr +\<^sub>p int p)"
      and head_no_alias:
        "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
          head +\<^sub>p int h \<noteq> head +\<^sub>p int bucket"
      and next_no_alias:
        "\<And>q p. \<lbrakk>q < unat src_len; p < unat src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      and next_head_disjoint:
        "\<And>h p. \<lbrakk>h < hash_size; p < unat src_len\<rbrakk> \<Longrightarrow>
          head +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
      and head_next_disjoint:
        "\<And>q bucket. \<lbrakk>q < unat src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int bucket"
  shows "build_index' src src_len head next_arr \<bullet> s
    \<lbrace> \<lambda>r t. r = Result () \<and>
        source_index_heap_rel t (heap_bytes s src (unat src_len)) head next_arr
        \<and> heap_typing t = heap_typing s \<rbrace>"
proof -
  have hashes:
    "build_index_hashes_ok s src src_len
      (heap_bytes s src (unat src_len))"
    by (rule build_index_hashes_okI[OF src_valid])
  show ?thesis
  proof (cases "src_len < (4 :: 32 word)")
  case True
  have head_valid_word:
    "\<And>idx. idx < (0x10000 :: 32 word) \<Longrightarrow>
      IS_VALID(32 word) s (head +\<^sub>p uint idx)"
  proof -
    fix idx :: "32 word"
    assume idx_lt: "idx < (0x10000 :: 32 word)"
    have idx_nat_lt: "unat idx < hash_size"
      using idx_lt by (simp add: word_less_nat_alt)
    have ptr_eq: "head +\<^sub>p uint idx = head +\<^sub>p int (unat idx)"
      by (simp only: uint_nat)
    show "IS_VALID(32 word) s (head +\<^sub>p uint idx)"
      apply (subst ptr_eq)
      by (rule head_valid[where st' = s and h = "unat idx", OF _ idx_nat_lt])
         simp
  qed
  show ?thesis
    by (rule build_index'_short_source_index_heap_rel[OF True head_valid_word])
next
  case False
  show ?thesis
    by (rule build_index'_long_source_index_heap_rel[
        OF False src_len_word hashes head_valid next_valid head_no_alias
          next_no_alias next_head_disjoint head_next_disjoint])
  qed
qed

lemma build_index'_source_index_heap_rel_buf_valid:
  fixes src :: "8 word ptr"
    and src_len :: "32 word"
    and head next_arr :: "32 word ptr"
  assumes src_len_word:
        "unat src_len < unat (no_entry32 :: 32 word)"
      and src_ok: "buf_valid s src (unat src_len)"
      and head_valid:
        "\<And>h (st' :: lifted_globals).
          \<lbrakk>heap_typing st' = heap_typing s; h < hash_size\<rbrakk> \<Longrightarrow>
          IS_VALID(32 word) st' (head +\<^sub>p int h)"
      and next_valid:
        "\<And>p (st' :: lifted_globals).
          \<lbrakk>heap_typing st' = heap_typing s; p < unat src_len\<rbrakk> \<Longrightarrow>
          IS_VALID(32 word) st' (next_arr +\<^sub>p int p)"
      and head_no_alias:
        "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
          head +\<^sub>p int h \<noteq> head +\<^sub>p int bucket"
      and next_no_alias:
        "\<And>q p. \<lbrakk>q < unat src_len; p < unat src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      and next_head_disjoint:
        "\<And>h p. \<lbrakk>h < hash_size; p < unat src_len\<rbrakk> \<Longrightarrow>
          head +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
      and head_next_disjoint:
        "\<And>q bucket. \<lbrakk>q < unat src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int bucket"
  shows "build_index' src src_len head next_arr \<bullet> s
    \<lbrace> \<lambda>r t. r = Result () \<and>
        source_index_heap_rel t (heap_bytes s src (unat src_len)) head next_arr
        \<and> heap_typing t = heap_typing s \<rbrace>"
proof (rule build_index'_source_index_heap_rel[
    OF src_len_word _ head_valid next_valid head_no_alias next_no_alias
      next_head_disjoint head_next_disjoint])
  fix off :: "32 word"
  fix st' :: lifted_globals
  assume typing: "heap_typing st' = heap_typing s"
  assume off_lt: "unat off < unat src_len"
  have ptr: "ptr_valid (heap_typing s) (src +\<^sub>p uint off)"
    by (rule buf_valid_uintD[OF src_ok off_lt])
  show "IS_VALID(8 word) st' (src +\<^sub>p uint off)"
    using ptr typing by simp
qed

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

lemma unat_suc_word_less:
  fixes n limit :: "32 word"
  assumes "n < limit"
  shows "unat (n + 1) = Suc (unat n)"
proof -
  have n_lt: "unat n < unat limit"
    using assms by (simp add: word_less_nat_alt)
  hence "unat n + unat (1 :: 32 word) < 2 ^ 32"
    using unat_lt2p[of limit] by simp
  thus ?thesis
    by (simp add: unat_word_ariths(1))
qed

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
