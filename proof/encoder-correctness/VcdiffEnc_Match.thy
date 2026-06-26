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

lemma reader_obind_SomeE:
  assumes "obind m f s = Some y"
  obtains x where "m s = Some x" "f x s = Some y"
  using assms by (cases "m s") (simp_all add: obind_def)

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

fun match_word_cursor :: "32 word list \<Rightarrow> nat \<Rightarrow> 32 word \<Rightarrow> 32 word" where
  "match_word_cursor next 0 cand = cand"
| "match_word_cursor next (Suc fuel) cand =
    (if cand = no_entry32 then no_entry32
     else if unat cand < length next then
       match_word_cursor next fuel (next ! unat cand)
     else cand)"

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

definition source_index_arrays_chains_closed ::
    "byte list \<Rightarrow> 32 word list \<Rightarrow> 32 word list \<Rightarrow> bool" where
  "source_index_arrays_chains_closed src heads nexts \<longleftrightarrow>
     length heads = hash_size \<and>
     length nexts = length src \<and>
     (\<forall>h < hash_size.
       (let bucket = index_bucket_spec (build_index_spec src) h in
        match_word_chain nexts (Suc (length bucket)) (heads ! h) = bucket))"

definition source_index_heap_chains_closed ::
    "lifted_globals \<Rightarrow> byte list \<Rightarrow> 32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow> bool" where
  "source_index_heap_chains_closed s src head_arr next_arr \<longleftrightarrow>
     source_index_arrays_chains_closed src
       (heap_w32_list s head_arr hash_size)
       (heap_w32_list s next_arr (length src))"

definition source_index_nexts_wf :: "byte list \<Rightarrow> 32 word list \<Rightarrow> bool" where
  "source_index_nexts_wf src nexts \<longleftrightarrow>
     length nexts = length src \<and>
     (\<forall>p. p + min_match \<le> length src \<longrightarrow>
       nexts ! p = no_entry32 \<or>
       unat (nexts ! p) + min_match \<le> length src)"

definition source_index_nexts_wf_from ::
    "byte list \<Rightarrow> nat \<Rightarrow> 32 word list \<Rightarrow> bool" where
  "source_index_nexts_wf_from src start nexts \<longleftrightarrow>
     length nexts = length src \<and>
     (\<forall>p. start \<le> p \<longrightarrow> p + min_match \<le> length src \<longrightarrow>
       nexts ! p = no_entry32 \<or>
       unat (nexts ! p) + min_match \<le> length src)"

definition source_index_heap_nexts_wf ::
    "lifted_globals \<Rightarrow> byte list \<Rightarrow> 32 word ptr \<Rightarrow> bool" where
  "source_index_heap_nexts_wf s src next_arr \<longleftrightarrow>
     source_index_nexts_wf src (heap_w32_list s next_arr (length src))"

definition source_index_heap_nexts_wf_from ::
    "lifted_globals \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> 32 word ptr \<Rightarrow> bool" where
  "source_index_heap_nexts_wf_from s src start next_arr \<longleftrightarrow>
     source_index_nexts_wf_from src start
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

definition source_index_arrays_chains_closed_from ::
    "byte list \<Rightarrow> nat \<Rightarrow> 32 word list \<Rightarrow> 32 word list \<Rightarrow> bool" where
  "source_index_arrays_chains_closed_from src start heads nexts \<longleftrightarrow>
     length heads = hash_size \<and>
     length nexts = length src \<and>
     (\<forall>h < hash_size.
       (let bucket = source_index_bucket_from src start h in
        match_word_chain nexts (Suc (length bucket)) (heads ! h) = bucket))"

definition source_index_heap_rel_from ::
    "lifted_globals \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow>
      32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow> bool" where
  "source_index_heap_rel_from s src start head_arr next_arr \<longleftrightarrow>
     source_index_arrays_rel_from src start
       (heap_w32_list s head_arr hash_size)
       (heap_w32_list s next_arr (length src))"

definition source_index_heap_chains_closed_from ::
    "lifted_globals \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow>
      32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow> bool" where
  "source_index_heap_chains_closed_from s src start head_arr next_arr \<longleftrightarrow>
     source_index_arrays_chains_closed_from src start
       (heap_w32_list s head_arr hash_size)
       (heap_w32_list s next_arr (length src))"

lemma heap_w32_list_length[simp]:
  "length (heap_w32_list s arr n) = n"
  by (simp add: heap_w32_list_def)

lemma heap_w32_list_nth[simp]:
  assumes "i < n"
  shows "heap_w32_list s arr n ! i = heap_w32 s (arr +\<^sub>p int i)"
  using assms by (simp add: heap_w32_list_def)

lemma source_index_heap_nexts_wfD:
  assumes wf: "source_index_heap_nexts_wf s src next_arr"
      and p_match: "p + min_match \<le> length src"
  shows "heap_w32 s (next_arr +\<^sub>p int p) = no_entry32 \<or>
         unat (heap_w32 s (next_arr +\<^sub>p int p)) + min_match \<le> length src"
proof -
  have p_lt: "p < length src"
    using p_match by (simp add: min_match_def)
  have nth_eq:
    "heap_w32_list s next_arr (length src) ! p =
     heap_w32 s (next_arr +\<^sub>p int p)"
    using p_lt by simp
  have list_ok:
    "heap_w32_list s next_arr (length src) ! p = no_entry32 \<or>
     unat (heap_w32_list s next_arr (length src) ! p) + min_match \<le> length src"
    using wf p_match
    unfolding source_index_heap_nexts_wf_def source_index_nexts_wf_def
    by blast
  show ?thesis
    using list_ok nth_eq by simp
qed

lemma source_index_heap_nexts_wf_len:
  assumes "source_index_heap_nexts_wf s src next_arr"
  shows "length (heap_w32_list s next_arr (length src)) = length src"
  using assms by simp

lemma source_index_nexts_wf_from_0:
  "source_index_nexts_wf_from src 0 nexts \<longleftrightarrow>
   source_index_nexts_wf src nexts"
  by (simp add: source_index_nexts_wf_from_def source_index_nexts_wf_def)

lemma source_index_heap_nexts_wf_from_0:
  "source_index_heap_nexts_wf_from s src 0 next_arr \<longleftrightarrow>
   source_index_heap_nexts_wf s src next_arr"
  by (simp add: source_index_heap_nexts_wf_from_def
      source_index_heap_nexts_wf_def source_index_nexts_wf_from_0)

lemma source_index_nexts_wf_from_empty:
  assumes nexts_len: "length nexts = length src"
      and start_ge: "length src - min_match + 1 \<le> start"
  shows "source_index_nexts_wf_from src start nexts"
  using assms
  by (auto simp: source_index_nexts_wf_from_def min_match_def)

lemma source_index_heap_nexts_wf_from_empty:
  assumes start_ge: "length src - min_match + 1 \<le> start"
  shows "source_index_heap_nexts_wf_from s src start next_arr"
  unfolding source_index_heap_nexts_wf_from_def
  apply (rule source_index_nexts_wf_from_empty)
   apply simp
  apply (rule start_ge)
  done

lemma source_index_nexts_wf_update:
  assumes wf: "source_index_nexts_wf src nexts"
      and p_match: "p + min_match \<le> length src"
      and v_ok: "v = no_entry32 \<or> unat v + min_match \<le> length src"
  shows "source_index_nexts_wf src (nexts[p := v])"
  using assms
  unfolding source_index_nexts_wf_def
  by (auto simp: min_match_def nth_list_update)

lemma source_index_nexts_wf_from_update:
  assumes wf: "source_index_nexts_wf_from src i nexts"
      and i_pos: "0 < i"
      and p_def: "p = i - 1"
      and p_match: "p + min_match \<le> length src"
      and v_ok: "v = no_entry32 \<or> unat v + min_match \<le> length src"
  shows "source_index_nexts_wf_from src p (nexts[p := v])"
proof -
  have nexts_len: "length nexts = length src"
    using wf by (simp add: source_index_nexts_wf_from_def)
  have p_lt: "p < length src"
    using p_match by (simp add: min_match_def)
  have p_lt_nexts: "p < length nexts"
    using p_lt nexts_len by simp
  show ?thesis
    unfolding source_index_nexts_wf_from_def
  proof (intro conjI allI impI)
    show "length (nexts[p := v]) = length src"
      using nexts_len by simp
  next
    fix q
    assume p_le_q: "p \<le> q"
    assume q_match: "q + min_match \<le> length src"
    have q_lt: "q < length src"
      using q_match by (simp add: min_match_def)
    show "(nexts[p := v]) ! q = no_entry32 \<or>
          unat ((nexts[p := v]) ! q) + min_match \<le> length src"
    proof (cases "q = p")
      case True
      then show ?thesis
        using v_ok p_lt_nexts by (simp add: nth_list_update)
    next
      case False
      have i_le_q: "i \<le> q"
        using p_def i_pos p_le_q False by arith
      have old_ok:
        "nexts ! q = no_entry32 \<or>
         unat (nexts ! q) + min_match \<le> length src"
        using wf i_le_q q_match
        unfolding source_index_nexts_wf_from_def by blast
      show ?thesis
        using old_ok False q_lt by simp
    qed
  qed
qed

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

lemma source_index_heap_nexts_wf_from_step:
  fixes next_arr head_arr :: "32 word ptr"
    and new_head :: "32 word"
  assumes wf: "source_index_heap_nexts_wf_from s src i next_arr"
      and i_pos: "0 < i"
      and p_def: "p = i - 1"
      and p_match: "p + min_match \<le> length src"
      and v_ok: "v = no_entry32 \<or> unat v + min_match \<le> length src"
      and next_no_alias:
        "\<And>q. q < length src \<Longrightarrow> q \<noteq> p \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      and head_next_disjoint:
        "\<And>q. q < length src \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> head_arr +\<^sub>p int bucket"
  defines "s_next \<equiv>
    heap_w32_update (\<lambda>a. a(next_arr +\<^sub>p int p := v)) s"
  defines "s_head \<equiv>
    heap_w32_update (\<lambda>ha. ha(head_arr +\<^sub>p int bucket := new_head)) s_next"
  shows "source_index_heap_nexts_wf_from s_head src p next_arr"
proof -
  let ?nexts = "heap_w32_list s next_arr (length src)"
  have wf_arrays: "source_index_nexts_wf_from src i ?nexts"
    using wf by (simp add: source_index_heap_nexts_wf_from_def)
  have p_lt: "p < length src"
    using p_match by (simp add: min_match_def)
  have nexts_after_next:
    "heap_w32_list s_next next_arr (length src) = ?nexts[p := v]"
    unfolding s_next_def
    apply (rule heap_w32_list_update_index)
      apply (rule p_lt)
     apply simp
    using next_no_alias
    apply auto
    done
  have nexts_after_head:
    "heap_w32_list s_head next_arr (length src) = ?nexts[p := v]"
    unfolding s_head_def
    apply (subst nexts_after_next[symmetric])
    apply (rule heap_w32_list_update_outside)
    using head_next_disjoint
    by auto
  have wf_after:
    "source_index_nexts_wf_from src p (?nexts[p := v])"
    by (rule source_index_nexts_wf_from_update[
        OF wf_arrays i_pos p_def p_match v_ok])
  show ?thesis
    using wf_after nexts_after_head
    by (simp add: source_index_heap_nexts_wf_from_def)
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

lemma source_index_arrays_chains_closed_from_0:
  "source_index_arrays_chains_closed_from src 0 heads nexts \<longleftrightarrow>
   source_index_arrays_chains_closed src heads nexts"
  by (simp add: source_index_arrays_chains_closed_from_def
      source_index_arrays_chains_closed_def)

lemma source_index_heap_chains_closed_from_0:
  "source_index_heap_chains_closed_from s src 0 head_arr next_arr \<longleftrightarrow>
   source_index_heap_chains_closed s src head_arr next_arr"
  by (simp add: source_index_heap_chains_closed_from_def
      source_index_heap_chains_closed_def
      source_index_arrays_chains_closed_from_0)

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

lemma source_index_arrays_chains_closed_from_empty:
  assumes heads_len: "length heads = hash_size"
      and nexts_len: "length nexts = length src"
      and heads_empty: "\<And>h. h < hash_size \<Longrightarrow> heads ! h = no_entry32"
      and start_ge: "length src - min_match + 1 \<le> start"
  shows "source_index_arrays_chains_closed_from src start heads nexts"
  unfolding source_index_arrays_chains_closed_from_def
proof (intro conjI allI impI)
  show "length heads = hash_size"
    using heads_len .
  show "length nexts = length src"
    using nexts_len .
  fix h
  assume h_lt: "h < hash_size"
  have bucket_empty: "source_index_bucket_from src start h = []"
    using start_ge
    by (simp add: source_index_bucket_from_def source_positions_from_empty)
  show "let bucket = source_index_bucket_from src start h in
        match_word_chain nexts (Suc (length bucket)) (heads ! h) = bucket"
    using bucket_empty heads_empty[OF h_lt] by simp
qed

lemma source_index_heap_chains_closed_from_empty:
  assumes heads_empty:
        "\<And>h. h < hash_size \<Longrightarrow>
          heap_w32 s (head_arr +\<^sub>p int h) = no_entry32"
      and start_ge: "length src - min_match + 1 \<le> start"
  shows "source_index_heap_chains_closed_from s src start head_arr next_arr"
  unfolding source_index_heap_chains_closed_from_def
  apply (rule source_index_arrays_chains_closed_from_empty)
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

lemma source_index_arrays_rel_from_head_wf:
  assumes rel: "source_index_arrays_rel_from src start heads nexts"
      and h_lt: "h < hash_size"
      and src_len_word: "length src \<le> unat (no_entry32 :: 32 word)"
  shows "heads ! h = no_entry32 \<or>
         unat (heads ! h) + min_match \<le> length src"
proof -
  let ?bucket = "source_index_bucket_from src start h"
  have rel_h:
    "let bucket = ?bucket in
      if bucket = [] then heads ! h = no_entry32
      else heads ! h = word_of_nat (hd bucket) \<and>
           match_word_chain nexts (length bucket) (heads ! h) = bucket"
    using rel h_lt
    unfolding source_index_arrays_rel_from_def by blast
  show ?thesis
  proof (cases "?bucket = []")
    case True
    then show ?thesis
      using rel_h by (simp add: Let_def)
  next
    case False
    have head_eq: "heads ! h = (of_nat (hd ?bucket) :: 32 word)"
      using rel_h False by (simp add: Let_def)
    have hd_in: "hd ?bucket \<in> set ?bucket"
      using False by simp
    have hd_bound: "hd ?bucket + min_match \<le> length src"
      using source_index_bucket_from_member_bounds[OF hd_in] by simp
    have hd_lt_src: "hd ?bucket < length src"
      using hd_bound by (simp add: min_match_def)
    have hd_lt_no_entry: "hd ?bucket < unat (no_entry32 :: 32 word)"
      using hd_bound src_len_word by (simp add: min_match_def)
    have unat_head: "unat (of_nat (hd ?bucket) :: 32 word) = hd ?bucket"
      using hd_lt_no_entry by (simp add: unat_of_nat_eq)
    show ?thesis
      using head_eq hd_bound unat_head by simp
  qed
qed

lemma source_index_heap_rel_from_head_wf:
  assumes rel: "source_index_heap_rel_from s src start head_arr next_arr"
      and h_lt: "h < hash_size"
      and src_len_word: "length src \<le> unat (no_entry32 :: 32 word)"
  shows "heap_w32 s (head_arr +\<^sub>p int h) = no_entry32 \<or>
         unat (heap_w32 s (head_arr +\<^sub>p int h)) + min_match \<le> length src"
proof -
  have arrays:
    "source_index_arrays_rel_from src start
      (heap_w32_list s head_arr hash_size)
      (heap_w32_list s next_arr (length src))"
    using rel by (simp add: source_index_heap_rel_from_def)
  have head_ok:
    "heap_w32_list s head_arr hash_size ! h = no_entry32 \<or>
     unat (heap_w32_list s head_arr hash_size ! h) + min_match \<le> length src"
    by (rule source_index_arrays_rel_from_head_wf[
        OF arrays h_lt src_len_word])
  show ?thesis
    using head_ok h_lt by simp
qed

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

lemma match_word_chain_head_member:
  assumes "0 < fuel"
      and "cand \<noteq> no_entry32"
      and "unat cand < length nexts"
  shows "unat cand \<in> set (match_word_chain nexts fuel cand)"
  using assms
  by (cases fuel) auto

lemma match_word_chain_tail_member:
  assumes "0 < fuel"
      and "cand \<noteq> no_entry32"
      and "unat cand < length nexts"
      and "p \<in> set (match_word_chain nexts (fuel - 1) (nexts ! unat cand))"
  shows "p \<in> set (match_word_chain nexts fuel cand)"
  using assms
  by (cases fuel) auto

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

lemma match_word_chain_closed_take:
  assumes closed: "match_word_chain nexts (Suc (length xs)) cand = xs"
  shows "match_word_chain nexts n cand = take n xs"
  using closed
proof (induction xs arbitrary: cand n)
  case Nil
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      by simp
  next
    case (Suc n')
    have stop: "cand = no_entry32 \<or> \<not> unat cand < length nexts"
      using Nil.prems by (auto split: if_splits)
    then show ?thesis
      using Suc by (cases n') auto
  qed
next
  case (Cons x xs)
  have cand_ok: "cand \<noteq> no_entry32" "unat cand < length nexts"
    using Cons.prems by (auto split: if_splits)
  have chain_unfold:
    "match_word_chain nexts (Suc (Suc (length xs))) cand =
     unat cand #
      match_word_chain nexts (Suc (length xs)) (nexts ! unat cand)"
    apply (subst match_word_chain.simps)
    using cand_ok by (simp only: if_False if_True)
  have len_eq: "Suc (length (x # xs)) = Suc (Suc (length xs))"
    by simp
  have chain_eq:
    "match_word_chain nexts (Suc (Suc (length xs))) cand = x # xs"
    using Cons.prems len_eq by metis
  have chain_cons:
    "unat cand #
      match_word_chain nexts (Suc (length xs)) (nexts ! unat cand) =
     x # xs"
    using chain_eq by (simp only: chain_unfold)
  have x_eq: "x = unat cand"
    using chain_cons by (metis list.inject)
  have tail_closed:
    "match_word_chain nexts (Suc (length xs)) (nexts ! unat cand) = xs"
    using chain_cons by (metis list.inject)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      by simp
  next
    case (Suc n')
    have tail:
      "match_word_chain nexts n' (nexts ! unat cand) = take n' xs"
      by (rule Cons.IH[OF tail_closed])
    show ?thesis
      using Suc cand_ok x_eq tail by simp
  qed
qed

lemma match_word_chain_append_cursor:
  "match_word_chain nexts (m + n) cand =
   match_word_chain nexts m cand @
   match_word_chain nexts n (match_word_cursor nexts m cand)"
proof (induction m arbitrary: cand)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  show ?case
  proof (cases "cand = no_entry32 \<or> \<not> unat cand < length nexts")
    case True
    then show ?thesis
      by (cases n) auto
  next
    case False
    then have cand_ok: "cand \<noteq> no_entry32" "unat cand < length nexts"
      by auto
    show ?thesis
      using Suc.IH[of "nexts ! unat cand"] cand_ok by simp
  qed
qed

lemma match_word_chain_Suc_cursor:
  assumes cand: "match_word_cursor nexts n cand0 = cand"
      and cand_not_noentry: "cand \<noteq> no_entry32"
      and cand_lt: "unat cand < length nexts"
  shows "match_word_chain nexts (Suc n) cand0 =
         match_word_chain nexts n cand0 @ [unat cand]"
proof -
  have "match_word_chain nexts (n + 1) cand0 =
        match_word_chain nexts n cand0 @
        match_word_chain nexts 1 (match_word_cursor nexts n cand0)"
    by (rule match_word_chain_append_cursor)
  thus ?thesis
    using assms by simp
qed

lemma match_word_cursor_Suc_step:
  assumes cand: "match_word_cursor nexts n cand0 = cand"
      and cand_not_noentry: "cand \<noteq> no_entry32"
      and cand_lt: "unat cand < length nexts"
  shows "match_word_cursor nexts (Suc n) cand0 = nexts ! unat cand"
proof -
  have "match_word_cursor nexts (n + 1) cand0 =
        match_word_cursor nexts 1 (match_word_cursor nexts n cand0)"
  proof (induction n arbitrary: cand0)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    show ?case
    proof (cases "cand0 = no_entry32 \<or> \<not> unat cand0 < length nexts")
      case True
      then show ?thesis
        by auto
    next
      case False
      then show ?thesis
        using Suc.IH[of "nexts ! unat cand0"] by simp
    qed
  qed
  thus ?thesis
    using assms by simp
qed

lemma match_word_chain_no_entry[simp]:
  "match_word_chain nexts n no_entry32 = []"
  by (cases n) simp_all

lemma match_word_chain_cursor_no_entry_prefix:
  assumes n_le: "n \<le> fuel"
      and cursor: "match_word_cursor nexts n cand0 = no_entry32"
  shows "match_word_chain nexts fuel cand0 =
         match_word_chain nexts n cand0"
proof -
  have fuel_eq: "fuel = n + (fuel - n)"
    using n_le by simp
  have "match_word_chain nexts fuel cand0 =
        match_word_chain nexts (n + (fuel - n)) cand0"
    using fuel_eq by simp
  also have "\<dots> =
        match_word_chain nexts n cand0 @
        match_word_chain nexts (fuel - n) (match_word_cursor nexts n cand0)"
    by (rule match_word_chain_append_cursor)
  also have "\<dots> = match_word_chain nexts n cand0"
    using cursor by simp
  finally show ?thesis .
qed

lemma match_word_chain_exit_prefix_max_chain:
  assumes n_le: "n \<le> max_chain"
      and cursor: "match_word_cursor nexts n cand0 = cand"
      and exit: "cand = no_entry32 \<or> n = max_chain"
  shows "match_word_chain nexts max_chain cand0 =
         match_word_chain nexts n cand0"
proof (cases "n = max_chain")
  case True
  then show ?thesis by simp
next
  case False
  with exit have cand_noentry: "cand = no_entry32"
    by simp
  show ?thesis
    by (rule match_word_chain_cursor_no_entry_prefix[
        OF n_le]) (simp add: cursor cand_noentry)
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

lemma match_word_chain_cons_update_closed:
  assumes p_lt: "p < length nexts"
      and p_unat: "unat (of_nat p :: 32 word) = p"
      and p_not_sentinel: "(of_nat p :: 32 word) \<noteq> no_entry32"
      and old_chain: "match_word_chain nexts (Suc fuel) old_head = bucket"
      and p_notin: "p \<notin> set bucket"
  shows "match_word_chain (nexts[p := old_head]) (Suc (Suc fuel)) (of_nat p) =
         p # bucket"
proof -
  have updated_tail:
    "match_word_chain (nexts[p := old_head]) (Suc fuel) old_head =
     match_word_chain nexts (Suc fuel) old_head"
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

lemma source_index_arrays_chains_closed_from_step:
  assumes closed: "source_index_arrays_chains_closed_from src i heads nexts"
      and src_long: "min_match \<le> length src"
      and i_pos: "0 < i"
      and i_le: "i \<le> length src - min_match + 1"
      and src_len_word: "length src < unat (no_entry32 :: 32 word)"
  defines "p \<equiv> i - 1"
  defines "bucket \<equiv> hash_bucket_spec src p"
  shows "source_index_arrays_chains_closed_from src p
    (heads[bucket := of_nat p]) (nexts[p := heads ! bucket])"
proof -
  have heads_len: "length heads = hash_size"
    using closed by (simp add: source_index_arrays_chains_closed_from_def)
  have nexts_len: "length nexts = length src"
    using closed by (simp add: source_index_arrays_chains_closed_from_def)
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
    unfolding source_index_arrays_chains_closed_from_def
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
    have old_closed:
      "match_word_chain nexts (Suc (length ?old)) (heads ! h) = ?old"
      using closed h_lt
      by (simp add: source_index_arrays_chains_closed_from_def Let_def)
    have p_notin_old: "p \<notin> set ?old"
    proof
      assume p_in: "p \<in> set ?old"
      have "i \<le> p"
        using source_index_bucket_from_member_bounds[OF p_in] by simp
      with i_pos show False
        by (simp add: p_def)
    qed
    show "let bucket = ?new in
        match_word_chain ?nexts' (Suc (length bucket)) (?heads' ! h) = bucket"
    proof (cases "bucket = h")
      case True
      have head_new: "?heads' ! h = of_nat p"
        using True bucket_lt heads_len by simp
      have chain_new:
        "match_word_chain ?nexts' (Suc (length ?new)) (?heads' ! h) = ?new"
        using match_word_chain_cons_update_closed[
            OF p_lt_nexts p_unat p_not_sentinel old_closed p_notin_old]
          bucket_step True head_new
        by simp
      show ?thesis
        using chain_new by simp
    next
      case False
      have head_same: "?heads' ! h = heads ! h"
        using False by simp
      have bucket_same: "?new = ?old"
        using bucket_step False by simp
      have chain_same:
        "match_word_chain ?nexts' (Suc (length ?old)) (heads ! h) = ?old"
      proof -
        have "p \<notin> set (match_word_chain nexts (Suc (length ?old)) (heads ! h))"
          using old_closed p_notin_old by simp
        hence "match_word_chain ?nexts' (Suc (length ?old)) (heads ! h) =
               match_word_chain nexts (Suc (length ?old)) (heads ! h)"
          by (rule match_word_chain_update_irrelevant)
        with old_closed show ?thesis by simp
      qed
      show ?thesis
        using bucket_same head_same chain_same by simp
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

lemma source_index_heap_chains_closed_from_step:
  fixes head_arr next_arr :: "32 word ptr"
  assumes closed:
      "source_index_heap_chains_closed_from s src i head_arr next_arr"
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
  shows "source_index_heap_chains_closed_from s_head src p head_arr next_arr"
proof -
  let ?heads = "heap_w32_list s head_arr hash_size"
  let ?nexts = "heap_w32_list s next_arr (length src)"
  have arrays_closed:
    "source_index_arrays_chains_closed_from src i ?heads ?nexts"
    using closed by (simp add: source_index_heap_chains_closed_from_def)
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
    "source_index_arrays_chains_closed_from src p
      (?heads[bucket := of_nat p]) (?nexts[p := ?heads ! bucket])"
  proof -
    have "source_index_arrays_chains_closed_from src (i - 1)
      (?heads[hash_bucket_spec src (i - 1) := of_nat (i - 1)])
      (?nexts[i - 1 := ?heads ! hash_bucket_spec src (i - 1)])"
      by (rule source_index_arrays_chains_closed_from_step[
          OF arrays_closed src_long i_pos i_le src_len_word])
    then show ?thesis
      by (simp add: p_def bucket_def)
  qed
  show ?thesis
    using arrays_after heads_after_head nexts_after_head
    by (simp add: source_index_heap_chains_closed_from_def)
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

lemma source_index_arrays_chains_closed_take_bucket_chain:
  assumes closed: "source_index_arrays_chains_closed src heads nexts"
      and h_lt: "h < hash_size"
  shows "match_word_chain nexts n (heads ! h) =
         take n (index_bucket_spec (build_index_spec src) h)"
proof -
  let ?bucket = "index_bucket_spec (build_index_spec src) h"
  have closed_h:
    "match_word_chain nexts (Suc (length ?bucket)) (heads ! h) = ?bucket"
    using closed h_lt
    by (simp add: source_index_arrays_chains_closed_def Let_def)
  show ?thesis
    by (rule match_word_chain_closed_take[OF closed_h])
qed

lemma source_index_heap_chains_closed_take_bucket_chain:
  assumes closed: "source_index_heap_chains_closed s src head_arr next_arr"
      and h_lt: "h < hash_size"
  shows "match_word_chain (heap_w32_list s next_arr (length src)) n
           (heap_w32 s (head_arr +\<^sub>p int h)) =
         take n (index_bucket_spec (build_index_spec src) h)"
proof -
  have arrays:
    "source_index_arrays_chains_closed src
      (heap_w32_list s head_arr hash_size)
      (heap_w32_list s next_arr (length src))"
    using closed by (simp add: source_index_heap_chains_closed_def)
  have chain:
    "match_word_chain (heap_w32_list s next_arr (length src)) n
       (heap_w32_list s head_arr hash_size ! h) =
     take n (index_bucket_spec (build_index_spec src) h)"
    by (rule source_index_arrays_chains_closed_take_bucket_chain[
        OF arrays h_lt])
  thus ?thesis
    using h_lt by simp
qed

lemma source_index_heap_chains_closed_max_chain_candidates:
  assumes closed: "source_index_heap_chains_closed s src head_arr next_arr"
      and h_lt: "h < hash_size"
  shows "match_word_chain (heap_w32_list s next_arr (length src)) max_chain
           (heap_w32 s (head_arr +\<^sub>p int h)) =
         take max_chain (index_bucket_spec (build_index_spec src) h)"
  by (rule source_index_heap_chains_closed_take_bucket_chain[
      OF closed h_lt])

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

lemma source_index_arrays_rel_short_chains_closed:
  assumes rel: "source_index_arrays_rel src heads nexts"
      and src_short: "length src < min_match"
  shows "source_index_arrays_chains_closed src heads nexts"
proof -
  have heads_len: "length heads = hash_size"
    using rel by (simp add: source_index_arrays_rel_def)
  have nexts_len: "length nexts = length src"
    using rel by (simp add: source_index_arrays_rel_def)
  show ?thesis
    unfolding source_index_arrays_chains_closed_def
  proof (intro conjI allI impI)
    show "length heads = hash_size"
      by (rule heads_len)
    show "length nexts = length src"
      by (rule nexts_len)
    fix h
    assume h_lt: "h < hash_size"
    have bucket_empty: "index_bucket_spec (build_index_spec src) h = []"
      using src_short h_lt
      by (simp add: index_bucket_spec_def build_index_spec_def source_positions_spec_def)
    have head_empty: "heads ! h = no_entry32"
      using rel h_lt bucket_empty
      by (simp add: source_index_arrays_rel_def Let_def)
    show "let bucket = index_bucket_spec (build_index_spec src) h in
        match_word_chain nexts (Suc (length bucket)) (heads ! h) = bucket"
      using bucket_empty head_empty by simp
  qed
qed

lemma source_index_heap_rel_short_chains_closed:
  assumes rel: "source_index_heap_rel s src head_arr next_arr"
      and src_short: "length src < min_match"
  shows "source_index_heap_chains_closed s src head_arr next_arr"
proof -
  have arrays:
    "source_index_arrays_rel src
      (heap_w32_list s head_arr hash_size)
      (heap_w32_list s next_arr (length src))"
    using rel by (simp add: source_index_heap_rel_def)
  have closed:
    "source_index_arrays_chains_closed src
      (heap_w32_list s head_arr hash_size)
      (heap_w32_list s next_arr (length src))"
    by (rule source_index_arrays_rel_short_chains_closed[OF arrays src_short])
  show ?thesis
    using closed by (simp add: source_index_heap_chains_closed_def)
qed

context vcdiff_enc_global_addresses begin

lemma source_index_heap_rel_take_chain_member_word_le:
  fixes cand src_len :: "32 word"
  assumes rel:
    "source_index_heap_rel s (heap_bytes s src (unat src_len)) head_arr next_arr"
      and h_lt: "h < hash_size"
      and cand_in: "unat cand \<in> set (match_word_chain
        (heap_w32_list s next_arr (unat src_len))
        (min n (length (index_bucket_spec
          (build_index_spec (heap_bytes s src (unat src_len))) h)))
        (heap_w32 s (head_arr +\<^sub>p int h)))"
  shows "cand \<le> src_len"
proof -
  have cand_in':
    "unat cand \<in> set (match_word_chain
      (heap_w32_list s next_arr (length (heap_bytes s src (unat src_len))))
      (min n (length (index_bucket_spec
        (build_index_spec (heap_bytes s src (unat src_len))) h)))
      (heap_w32 s (head_arr +\<^sub>p int h)))"
    using cand_in by simp
  have member:
    "unat cand + min_match \<le> length (heap_bytes s src (unat src_len)) \<and>
     hash_bucket_spec (heap_bytes s src (unat src_len)) (unat cand) = h"
    by (rule source_index_heap_rel_take_chain_member_sound[OF rel h_lt cand_in'])
  have "unat cand \<le> unat src_len"
    using member by simp
  thus ?thesis
    by (simp add: word_le_nat_alt)
qed

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

lemma hash_mask_word_unat_lt_hash_size:
  fixes w :: "32 word"
  shows "unat (w && 0xFFFF) < hash_size"
proof -
  have mask_eq:
    "w && 0xFFFF = (of_nat (unat w mod hash_size) :: 32 word)"
    using word32_hash_mask_of_nat[of "unat w"] by simp
  show ?thesis
    using mod_less_divisor[of hash_size "unat w"]
    by (simp add: mask_eq hash_size_def hash_bits_def unat_of_nat)
qed

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

lemma hash4'_heap_bytes_buf_valid:
  fixes src :: "8 word ptr"
    and p src_len :: "32 word"
  assumes len: "unat p + min_match \<le> unat src_len"
      and src_ok: "buf_valid st src (unat src_len)"
  shows "hash4' src p st =
    Some (of_nat
      (hash4_spec (heap_bytes st src (unat src_len)) (unat p)) :: 32 word)"
proof (rule hash4'_heap_bytes[
    where n = "unat src_len" and src_bytes = "heap_bytes st src (unat src_len)"])
  show "heap_bytes st src (unat src_len) =
      heap_bytes st src (unat src_len)"
    by simp
  show "unat p + min_match \<le> length (heap_bytes st src (unat src_len))"
    using len by simp
  show "length (heap_bytes st src (unat src_len)) < 2 ^ 32"
    using unat_lt2p[of src_len] by simp
  fix k
  assume k_lt: "k < min_match"
  have no_overflow: "unat p + unat (4 :: 32 word) < 2 ^ 32"
    using len unat_lt2p[of src_len] by (simp add: min_match_def)
  have idx: "unat (p + of_nat k :: 32 word) = unat p + k"
    by (rule unat_add_of_nat_index[where sz = "4", OF _ no_overflow])
       (use k_lt in \<open>simp add: min_match_def\<close>)
  have idx_lt: "unat (p + of_nat k :: 32 word) < unat src_len"
    using len k_lt by (simp add: idx min_match_def)
  show "IS_VALID(8 word) st (src +\<^sub>p uint (p + of_nat k :: 32 word))"
    by (rule buf_valid_uintD[OF src_ok idx_lt])
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
     source_index_heap_rel_from st src_bytes (unat i) head_arr next_arr \<and>
     source_index_heap_chains_closed_from st src_bytes (unat i) head_arr next_arr \<and>
     source_index_heap_nexts_wf_from st src_bytes (unat i) next_arr"

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
  have closed:
    "source_index_heap_chains_closed_from st src_bytes (unat i) head next_arr"
    using inv by (simp add: build_index_fill_inv_def)
  have nexts_wf:
    "source_index_heap_nexts_wf_from st src_bytes (unat i) next_arr"
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
  have head_value_wf:
    "heap_w32 st (head +\<^sub>p int ?bucket) = no_entry32 \<or>
     unat (heap_w32 st (head +\<^sub>p int ?bucket)) + min_match \<le> length src_bytes"
    apply (rule source_index_heap_rel_from_head_wf[OF rel bucket_lt])
    using src_len_word by simp
  have step_nexts_wf:
    "source_index_heap_nexts_wf_from ?s_head src_bytes ?p next_arr"
  proof (rule source_index_heap_nexts_wf_from_step[
      where i = "unat i" and s = st and p = ?p and bucket = ?bucket
        and v = "heap_w32 st (head +\<^sub>p int ?bucket)"
        and new_head = "of_nat ?p" and head_arr = head])
    show "source_index_heap_nexts_wf_from st src_bytes (unat i) next_arr"
      by (rule nexts_wf)
    show "0 < unat i"
      by (rule i_pos_nat)
    show "?p = unat i - 1"
      by (rule p_unat)
    show "?p + min_match \<le> length src_bytes"
      by (rule p_match_bound)
    show "heap_w32 st (head +\<^sub>p int ?bucket) = no_entry32 \<or>
        unat (heap_w32 st (head +\<^sub>p int ?bucket)) + min_match \<le> length src_bytes"
      by (rule head_value_wf)
    show "\<And>q. q < length src_bytes \<Longrightarrow> q \<noteq> ?p \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int ?p"
    proof -
      fix q
      assume q_lt: "q < length src_bytes"
      assume q_ne: "q \<noteq> ?p"
      show "next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int ?p"
        by (rule next_no_alias[OF q_lt p_lt_src q_ne])
    qed
    show "\<And>q. q < length src_bytes \<Longrightarrow>
        next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int ?bucket"
    proof -
      fix q
      assume q_lt: "q < length src_bytes"
      show "next_arr +\<^sub>p int q \<noteq> head +\<^sub>p int ?bucket"
        by (rule head_next_disjoint[OF q_lt bucket_lt])
    qed
  qed
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
  have step_closed:
    "source_index_heap_chains_closed_from ?s_head src_bytes ?p head next_arr"
  proof (rule source_index_heap_chains_closed_from_step[
      where i = "unat i" and s = st and p = ?p and bucket = ?bucket])
    show "source_index_heap_chains_closed_from st src_bytes (unat i) head next_arr"
      by (rule closed)
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
  have step_closed_c:
    "source_index_heap_chains_closed_from
      (heap_w32_update
        (\<lambda>ha. ha(head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF) :=
          ?p_word))
        (heap_w32_update
          (\<lambda>a. a(next_arr +\<^sub>p uint ?p_word :=
            a (head +\<^sub>p uint ((of_nat ?hash :: 32 word) && 0xFFFF)))) st))
      src_bytes (unat ?p_word) head next_arr"
    by (subst final_state_eq, rule step_closed)
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
  have step_nexts_wf_c:
    "source_index_heap_nexts_wf_from ?st_c src_bytes (unat ?p_word) next_arr"
    by (subst final_state_eq, rule step_nexts_wf)
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
      apply (rule step_closed_c)
    apply (rule step_nexts_wf_c)
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

lemma build_index_fill_loop_source_index_heap_rel_nexts_wf:
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
      source_index_heap_nexts_wf t src_bytes next_arr \<and>
      source_index_heap_chains_closed t src_bytes head next_arr \<and>
      heap_typing t = heap_typing s0\<rbrace>"
  apply (rule runs_to_weaken[OF build_index_fill_loop_preserves_inv[
        OF inv0 hashes]])
        apply (auto intro: head_valid next_valid
          dest: head_no_alias next_no_alias next_head_disjoint
            head_next_disjoint
          simp: build_index_fill_inv_def source_index_heap_rel_from_0
            source_index_heap_nexts_wf_from_0
            source_index_heap_chains_closed_from_0)
  apply (metis head_no_alias hash_size_0x10000)
  done

lemma build_index_fill_loop_source_index_heap_rel_nexts_wf_bytes:
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
      source_index_heap_nexts_wf t src_bytes next_arr \<and>
      source_index_heap_chains_closed t src_bytes head next_arr \<and>
      heap_typing t = heap_typing s0 \<and>
      heap_bytes t src (unat src_len) = src_bytes\<rbrace>"
  apply (rule runs_to_weaken[OF build_index_fill_loop_preserves_inv[
        OF inv0 hashes]])
        apply (auto intro: head_valid next_valid
          dest: head_no_alias next_no_alias next_head_disjoint
            head_next_disjoint
          simp: build_index_fill_inv_def source_index_heap_rel_from_0
            source_index_heap_nexts_wf_from_0
            source_index_heap_chains_closed_from_0)
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

lemma build_index'_short_source_index_heap_rel_bytes:
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
        \<and> heap_typing t = heap_typing s
        \<and> heap_bytes t src (unat src_len) =
          heap_bytes s src (unat src_len) \<rbrace>"
proof -
  let ?src_bytes = "heap_bytes s src (unat src_len)"
  have init:
    "(whileLoop (\<lambda>(idx :: 32 word) st. idx < 0x10000)
      (\<lambda>idx. do {
          guard (\<lambda>st. IS_VALID(32 word) st (head +\<^sub>p uint idx));
          modify (heap_w32_update
            (\<lambda>h. h(head +\<^sub>p uint idx := no_entry32)));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
    \<lbrace> \<lambda>r t. r = Result (0x10000 :: 32 word)
          \<and> heap_typing t = heap_typing s
          \<and> (\<forall>h < hash_size. heap_w32 t (head +\<^sub>p int h) = no_entry32)
          \<and> heap_bytes t src (unat src_len) = ?src_bytes \<rbrace>"
    by (rule build_index_head_init_loop[
        where src = src and n = "unat src_len", OF head_valid])
  show ?thesis
    unfolding build_index'_def
    apply runs_to_vcg
    subgoal
      apply (rule runs_to_weaken[OF init])
       apply simp
      subgoal premises prems for t
      proof -
        have typing_t: "heap_typing t = heap_typing s"
          using prems by simp
        have heads_empty:
          "\<And>h. h < hash_size \<Longrightarrow>
            heap_w32 t (head +\<^sub>p int h) = no_entry32"
          using prems by simp
        have bytes_t: "heap_bytes t src (unat src_len) = ?src_bytes"
          using prems by simp
        have arrays:
          "source_index_arrays_rel ?src_bytes
            (heap_w32_list t head hash_size)
            (heap_w32_list t next_arr (length ?src_bytes))"
        proof (rule source_index_arrays_rel_short)
          show "length ?src_bytes < min_match"
            using src_short by (simp add: word_less_nat_alt min_match_def)
        next
          show "length (heap_w32_list t head hash_size) = hash_size"
            by simp
        next
          show "length (heap_w32_list t next_arr (length ?src_bytes)) =
            length ?src_bytes"
            by simp
        next
          fix h
          assume h_lt: "h < hash_size"
          show "heap_w32_list t head hash_size ! h = no_entry32"
            using heads_empty[OF h_lt] h_lt by simp
        qed
        show ?thesis
          using arrays typing_t bytes_t src_short
          by (simp add: source_index_heap_rel_def)
      qed
      done
    done
qed

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
        \<and> source_index_heap_nexts_wf t
          (heap_bytes s src (unat src_len)) next_arr
        \<and> source_index_heap_chains_closed t
          (heap_bytes s src (unat src_len)) head next_arr
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
        have init_nexts_wf:
          "source_index_heap_nexts_wf_from t ?src_bytes (unat ?start) next_arr"
          by (rule source_index_heap_nexts_wf_from_empty[OF start_ge])
        have init_closed:
          "source_index_heap_chains_closed_from t ?src_bytes (unat ?start) head next_arr"
        proof (rule source_index_heap_chains_closed_from_empty)
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
          apply (rule init_closed)
          apply (rule init_nexts_wf)
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
            source_index_heap_nexts_wf t ?src_bytes next_arr \<and>
            source_index_heap_chains_closed t ?src_bytes head next_arr \<and>
            heap_typing t = heap_typing s\<rbrace>"
          apply (rule build_index_fill_loop_source_index_heap_rel_nexts_wf[
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
            source_index_heap_nexts_wf t ?src_bytes next_arr \<and>
            source_index_heap_chains_closed t ?src_bytes head next_arr \<and>
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

lemma build_index'_long_source_index_heap_rel_nexts_wf_chains_closed_bytes:
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
        \<and> source_index_heap_nexts_wf t
          (heap_bytes s src (unat src_len)) next_arr
        \<and> source_index_heap_chains_closed t
          (heap_bytes s src (unat src_len)) head next_arr
        \<and> heap_typing t = heap_typing s
        \<and> heap_bytes t src (unat src_len) =
          heap_bytes s src (unat src_len) \<rbrace>"
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
        have init_nexts_wf:
          "source_index_heap_nexts_wf_from t ?src_bytes (unat ?start) next_arr"
          by (rule source_index_heap_nexts_wf_from_empty[OF start_ge])
        have init_closed:
          "source_index_heap_chains_closed_from t ?src_bytes (unat ?start) head next_arr"
        proof (rule source_index_heap_chains_closed_from_empty)
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
          apply (rule init_closed)
          apply (rule init_nexts_wf)
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
            source_index_heap_nexts_wf t ?src_bytes next_arr \<and>
            source_index_heap_chains_closed t ?src_bytes head next_arr \<and>
            heap_typing t = heap_typing s \<and>
            heap_bytes t src (unat src_len) = ?src_bytes\<rbrace>"
          apply (rule build_index_fill_loop_source_index_heap_rel_nexts_wf_bytes[
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
            source_index_heap_nexts_wf t ?src_bytes next_arr \<and>
            source_index_heap_chains_closed t ?src_bytes head next_arr \<and>
            heap_typing t = heap_typing s \<and>
            heap_bytes t src (unat src_len) = ?src_bytes\<rbrace>"
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
    have long:
      "build_index' src src_len head next_arr \<bullet> s
        \<lbrace> \<lambda>r t. r = Result () \<and>
            source_index_heap_rel t
              (heap_bytes s src (unat src_len)) head next_arr \<and>
            source_index_heap_nexts_wf t
              (heap_bytes s src (unat src_len)) next_arr \<and>
            source_index_heap_chains_closed t
              (heap_bytes s src (unat src_len)) head next_arr \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule build_index'_long_source_index_heap_rel[
          OF False src_len_word hashes head_valid next_valid head_no_alias
            next_no_alias next_head_disjoint head_next_disjoint])
    show ?thesis
      apply (rule runs_to_weaken[OF long])
      apply simp
      done
  qed
qed

lemma build_index'_source_index_heap_rel_nexts_wf:
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
        \<and> source_index_heap_nexts_wf t
          (heap_bytes s src (unat src_len)) next_arr
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
    have short:
      "build_index' src src_len head next_arr \<bullet> s
        \<lbrace> \<lambda>r t. r = Result () \<and>
            source_index_heap_rel t
              (heap_bytes s src (unat src_len)) head next_arr \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule build_index'_short_source_index_heap_rel[
            OF True head_valid_word])
    show ?thesis
      apply (rule runs_to_weaken[OF short])
      apply (insert True)
      apply (clarsimp simp: source_index_heap_nexts_wf_def
          source_index_nexts_wf_def min_match_def word_less_nat_alt)
      done
  next
    case False
    have long:
      "build_index' src src_len head next_arr \<bullet> s
        \<lbrace> \<lambda>r t. r = Result () \<and>
            source_index_heap_rel t
              (heap_bytes s src (unat src_len)) head next_arr \<and>
            source_index_heap_nexts_wf t
              (heap_bytes s src (unat src_len)) next_arr \<and>
            source_index_heap_chains_closed t
              (heap_bytes s src (unat src_len)) head next_arr \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule build_index'_long_source_index_heap_rel[
          OF False src_len_word hashes head_valid next_valid head_no_alias
            next_no_alias next_head_disjoint head_next_disjoint])
    show ?thesis
      apply (rule runs_to_weaken[OF long])
      apply simp
      done
  qed
qed

lemma build_index'_source_index_heap_rel_nexts_wf_chains_closed:
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
        \<and> source_index_heap_nexts_wf t
          (heap_bytes s src (unat src_len)) next_arr
        \<and> source_index_heap_chains_closed t
          (heap_bytes s src (unat src_len)) head next_arr
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
    have short:
      "build_index' src src_len head next_arr \<bullet> s
        \<lbrace> \<lambda>r t. r = Result () \<and>
            source_index_heap_rel t
              (heap_bytes s src (unat src_len)) head next_arr \<and>
            heap_typing t = heap_typing s \<rbrace>"
      by (rule build_index'_short_source_index_heap_rel[
            OF True head_valid_word])
    show ?thesis
      apply (rule runs_to_weaken[OF short])
      apply (insert True)
      apply (clarsimp simp: source_index_heap_nexts_wf_def
          source_index_nexts_wf_def min_match_def word_less_nat_alt)
      apply (rule source_index_heap_rel_short_chains_closed)
       apply assumption
      apply (simp add: min_match_def word_less_nat_alt)
      done
  next
    case False
    show ?thesis
      by (rule build_index'_long_source_index_heap_rel[
          OF False src_len_word hashes head_valid next_valid head_no_alias
            next_no_alias next_head_disjoint head_next_disjoint])
  qed
qed

lemma build_index'_source_index_heap_rel_nexts_wf_chains_closed_bytes:
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
        \<and> source_index_heap_nexts_wf t
          (heap_bytes s src (unat src_len)) next_arr
        \<and> source_index_heap_chains_closed t
          (heap_bytes s src (unat src_len)) head next_arr
        \<and> heap_typing t = heap_typing s
        \<and> heap_bytes t src (unat src_len) =
          heap_bytes s src (unat src_len) \<rbrace>"
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
    have short:
      "build_index' src src_len head next_arr \<bullet> s
        \<lbrace> \<lambda>r t. r = Result () \<and>
            source_index_heap_rel t
              (heap_bytes s src (unat src_len)) head next_arr \<and>
            heap_typing t = heap_typing s \<and>
            heap_bytes t src (unat src_len) =
              heap_bytes s src (unat src_len) \<rbrace>"
      by (rule build_index'_short_source_index_heap_rel_bytes[
            OF True head_valid_word])
    show ?thesis
      apply (rule runs_to_weaken[OF short])
      apply (insert True)
      apply (clarsimp simp: source_index_heap_nexts_wf_def
          source_index_nexts_wf_def min_match_def word_less_nat_alt)
      apply (rule source_index_heap_rel_short_chains_closed)
       apply assumption
      apply (simp add: min_match_def word_less_nat_alt)
      done
  next
    case False
    show ?thesis
      by (rule build_index'_long_source_index_heap_rel_nexts_wf_chains_closed_bytes[
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

lemma build_index'_source_index_heap_rel_nexts_wf_buf_valid:
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
        \<and> source_index_heap_nexts_wf t
          (heap_bytes s src (unat src_len)) next_arr
        \<and> heap_typing t = heap_typing s \<rbrace>"
proof (rule build_index'_source_index_heap_rel_nexts_wf[
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

lemma build_index'_source_index_heap_rel_nexts_wf_chains_closed_buf_valid:
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
        \<and> source_index_heap_nexts_wf t
          (heap_bytes s src (unat src_len)) next_arr
        \<and> source_index_heap_chains_closed t
          (heap_bytes s src (unat src_len)) head next_arr
        \<and> heap_typing t = heap_typing s \<rbrace>"
proof (rule build_index'_source_index_heap_rel_nexts_wf_chains_closed[
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

lemma build_index'_source_index_heap_rel_nexts_wf_chains_closed_bytes_buf_valid:
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
        \<and> source_index_heap_nexts_wf t
          (heap_bytes s src (unat src_len)) next_arr
        \<and> source_index_heap_chains_closed t
          (heap_bytes s src (unat src_len)) head next_arr
        \<and> heap_typing t = heap_typing s
        \<and> heap_bytes t src (unat src_len) =
          heap_bytes s src (unat src_len) \<rbrace>"
proof (rule build_index'_source_index_heap_rel_nexts_wf_chains_closed_bytes[
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

lemma unat_suc_measure_decreases:
  fixes n limit :: "32 word"
  assumes "unat n < unat limit"
  shows "unat limit - unat (n + 1) < unat limit - unat n"
proof -
  have n_lt: "n < limit"
    using assms by (simp add: word_less_nat_alt)
  have n_suc_unat: "unat (n + 1) = Suc (unat n)"
    by (rule unat_suc_word_less[OF n_lt])
  show ?thesis
    using assms n_suc_unat by simp
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

lemma common_prefix_fuel_eqI:
  assumes l_le: "l \<le> fuel"
      and prefix:
        "\<And>i. i < l \<Longrightarrow>
          apos + i < length a \<and>
          bpos + i < length b \<and>
          a ! (apos + i) = b ! (bpos + i)"
      and stop:
        "l = fuel \<or>
         apos + l \<ge> length a \<or>
         bpos + l \<ge> length b \<or>
         a ! (apos + l) \<noteq> b ! (bpos + l)"
  shows "common_prefix_fuel fuel a apos b bpos = l"
  using assms
proof (induction fuel arbitrary: apos bpos l)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases l)
    case 0
    have stop0:
      "apos \<ge> length a \<or>
       bpos \<ge> length b \<or>
       a ! apos \<noteq> b ! bpos"
      using Suc.prems(3) 0 by auto
    show ?thesis
      using 0 stop0 by auto
  next
    case (Suc l')
    have cond:
      "apos < length a \<and> bpos < length b \<and> a ! apos = b ! bpos"
      using Suc.prems(2)[of 0] Suc by simp
    have l'_le: "l' \<le> fuel"
      using Suc.prems(1) Suc by simp
    have prefix':
      "\<And>i. i < l' \<Longrightarrow>
        (apos + 1) + i < length a \<and>
        (bpos + 1) + i < length b \<and>
        a ! ((apos + 1) + i) = b ! ((bpos + 1) + i)"
    proof -
      fix i
      assume i_lt: "i < l'"
      have "Suc i < l"
        using i_lt Suc by simp
      have step: "apos + Suc i = (apos + 1) + i"
        by simp
      have step_b: "bpos + Suc i = (bpos + 1) + i"
        by simp
      show "(apos + 1) + i < length a \<and>
        (bpos + 1) + i < length b \<and>
        a ! ((apos + 1) + i) = b ! ((bpos + 1) + i)"
        using Suc.prems(2)[OF \<open>Suc i < l\<close>]
        by (simp add: step step_b)
    qed
    have stop':
      "l' = fuel \<or>
       (apos + 1) + l' \<ge> length a \<or>
       (bpos + 1) + l' \<ge> length b \<or>
       a ! ((apos + 1) + l') \<noteq> b ! ((bpos + 1) + l')"
      using Suc.prems(3) Suc by auto
    have rec:
      "common_prefix_fuel fuel a (apos + 1) b (bpos + 1) = l'"
      by (rule Suc.IH[OF l'_le prefix' stop'])
    show ?thesis
      using Suc cond rec by simp
  qed
qed

lemma common_prefix'_result_sound_word:
  fixes src tgt :: "8 word ptr"
    and cand src_len tp tgt_len l :: "32 word"
  assumes result:
    "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
  defines "limit \<equiv>
    (if src_len - cand < tgt_len - tp then src_len - cand else tgt_len - tp)"
  shows "unat l \<le> unat limit \<and>
    (\<forall>i < unat l.
      heap_w8 s (src +\<^sub>p uint (cand + of_nat i :: 32 word)) =
      heap_w8 s (tgt +\<^sub>p uint (tp + of_nat i :: 32 word)))"
proof -
  let ?eq = "\<lambda>i.
    heap_w8 s (src +\<^sub>p uint (cand + of_nat i :: 32 word)) =
    heap_w8 s (tgt +\<^sub>p uint (tp + of_nat i :: 32 word))"
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
                    (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                  IS_VALID(8 word) st
                    (src +\<^sub>p uint (cand + (n + 1))));
             ogets
              (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                      heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                   then 1 else 0)
           })
          (oreturn 0);
      oreturn (n + 1, ret)
    }"
  let ?I = "\<lambda>(n :: 32 word, ret :: int) s.
    unat n \<le> unat limit \<and>
    (\<forall>i < unat n. ?eq i) \<and>
    (ret \<noteq> 0 \<longrightarrow> unat n < unat limit \<and> ?eq (unat n))"
  have body_preserves:
    "\<And>n ret n' ret'. \<lbrakk>?I (n, ret) s; ret \<noteq> 0;
      ?B (n, ret) s = Some (n', ret')\<rbrakk> \<Longrightarrow> ?I (n', ret') s"
  proof -
    fix n n' :: "32 word"
    fix ret ret' :: int
    assume inv: "?I (n, ret) s"
    assume ret_ne: "ret \<noteq> 0"
    assume body: "?B (n, ret) s = Some (n', ret')"
    have n_lt: "unat n < unat limit"
      using inv ret_ne by simp
    have n_word_lt: "n < limit"
      using n_lt by (simp add: word_less_nat_alt)
    have n_suc_unat: "unat (n + 1) = Suc (unat n)"
      by (rule unat_suc_word_less[OF n_word_lt])
    have n_suc_le: "unat (n + 1) \<le> unat limit"
      using n_lt n_suc_unat by simp
    have old_eq: "\<And>i. i < unat n \<Longrightarrow> ?eq i"
      using inv by simp
    have n_eq: "?eq (unat n)"
      using inv ret_ne by simp
    have n'_eq: "n' = n + 1"
      using body
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits)
    have prefix_eq: "\<And>i. i < unat (n + 1) \<Longrightarrow> ?eq i"
    proof -
      fix i
      assume "i < unat (n + 1)"
      hence "i < unat n \<or> i = unat n"
        using n_suc_unat by (simp add: less_Suc_eq)
      thus "?eq i"
        using old_eq n_eq by auto
    qed
    have ret_pos:
      "ret' \<noteq> 0 \<Longrightarrow>
        n + 1 < limit \<and>
        heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
        heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))"
      using body
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits)
    have ret_inv:
      "ret' \<noteq> 0 \<Longrightarrow> unat (n + 1) < unat limit \<and> ?eq (unat (n + 1))"
    proof -
      assume ret'_ne: "ret' \<noteq> 0"
      have word_lt: "n + 1 < limit"
        and word_eq:
          "heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
           heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))"
        using ret_pos[OF ret'_ne] by auto
      show ?thesis
        using word_lt word_eq by (simp add: word_less_nat_alt)
    qed
    show "?I (n', ret') s"
      using n'_eq n_suc_le prefix_eq ret_inv by auto
  qed
  have body_decreases:
    "\<And>n ret n' ret'. \<lbrakk>?I (n, ret) s; ret \<noteq> 0;
      ?B (n, ret) s = Some (n', ret')\<rbrakk> \<Longrightarrow>
      unat limit - unat n' < unat limit - unat n"
  proof (goal_cases)
    case (1 n ret n' ret')
    have n_lt: "unat n < unat limit"
      using 1 by simp
    have n_word_lt: "n < limit"
      using n_lt by (simp add: word_less_nat_alt)
    have n_suc_unat: "unat (n + 1) = Suc (unat n)"
      by (rule unat_suc_word_less[OF n_word_lt])
    have n'_eq: "n' = n + 1"
      using 1
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits)
    have dec:
      "unat limit - unat (n + 1) < unat limit - unat n"
      using n_lt n_suc_unat by simp
    show ?case
      using dec n'_eq by simp
  qed
  have body_preserves_step:
    "\<And>n ret ret'. \<lbrakk>?I (n, ret) s; ret \<noteq> 0;
      ocondition
        (\<lambda>s. n + 1 < limit)
        (do {
           oguard
            (\<lambda>st.
                IS_VALID(8 word) st (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                IS_VALID(8 word) st (src +\<^sub>p uint (cand + (n + 1))));
           ogets
            (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                    heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                 then 1 else 0)
         })
        (oreturn 0) s = Some ret'\<rbrakk> \<Longrightarrow>
      ?I (n + 1, ret') s"
  proof -
    fix n :: "32 word"
    fix ret ret' :: int
    assume inv: "?I (n, ret) s"
    assume ret_ne: "ret \<noteq> 0"
    assume step:
      "ocondition
        (\<lambda>s. n + 1 < limit)
        (do {
           oguard
            (\<lambda>st.
                IS_VALID(8 word) st (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                IS_VALID(8 word) st (src +\<^sub>p uint (cand + (n + 1))));
           ogets
            (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                    heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                 then 1 else 0)
         })
        (oreturn 0) s = Some ret'"
    have body: "?B (n, ret) s = Some (n + 1, ret')"
      using step by (simp add: obind_def oreturn_def K_def)
    show "?I (n + 1, ret') s"
      by (rule body_preserves[OF inv ret_ne body])
  qed
  have body_preserves_step_pos:
    "\<And>n ret'. \<lbrakk>
      \<forall>i < unat n. ?eq i;
      unat n < unat limit;
      ?eq (unat n);
      ocondition
        (\<lambda>s. n + 1 < limit)
        (do {
           oguard
            (\<lambda>st.
                IS_VALID(8 word) st (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                IS_VALID(8 word) st (src +\<^sub>p uint (cand + (n + 1))));
           ogets
            (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                    heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                 then 1 else 0)
         })
        (oreturn 0) s = Some ret'\<rbrakk> \<Longrightarrow>
      ?I (n + 1, ret') s"
  proof -
    fix n :: "32 word"
    fix ret' :: int
    assume prefix: "\<forall>i < unat n. ?eq i"
    assume n_lt: "unat n < unat limit"
    assume n_eq: "?eq (unat n)"
    assume step:
      "ocondition
        (\<lambda>s. n + 1 < limit)
        (do {
           oguard
            (\<lambda>st.
                IS_VALID(8 word) st (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                IS_VALID(8 word) st (src +\<^sub>p uint (cand + (n + 1))));
           ogets
            (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                    heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                 then 1 else 0)
         })
        (oreturn 0) s = Some ret'"
    have inv: "?I (n, 1) s"
      using prefix n_lt n_eq by simp
    show "?I (n + 1, ret') s"
      by (rule body_preserves_step[OF inv _ step]) simp
  qed
  have body_preserves_expanded:
    "\<And>(n :: 32 word) (n' :: 32 word) (ret' :: int). \<lbrakk>
      \<forall>i < unat n. ?eq i;
      unat n < unat limit;
      ?eq (unat n);
      (do {
         ret <-
           ocondition
            (\<lambda>s. n + 1 < limit)
            (do {
               oguard
                (\<lambda>st.
                    IS_VALID(8 word) st (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                    IS_VALID(8 word) st (src +\<^sub>p uint (cand + (n + 1))));
               ogets
                (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                        heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                     then 1 else 0)
             })
            (oreturn 0);
         oreturn (n + 1, ret)
       }) s = Some (n', ret')\<rbrakk> \<Longrightarrow>
      unat n' \<le> unat limit \<and>
      (\<forall>i < unat n'. ?eq i) \<and>
      (ret' \<noteq> 0 \<longrightarrow> unat n' < unat limit \<and> ?eq (unat n'))"
  proof (goal_cases)
    case (1 n n' ret')
    have n'_eq: "n' = n + 1"
      using 1(4)
      by (auto simp: obind_def oreturn_def K_def split: option.splits)
    have step:
      "ocondition
        (\<lambda>s. n + 1 < limit)
        (do {
           oguard
            (\<lambda>st.
                IS_VALID(8 word) st (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                IS_VALID(8 word) st (src +\<^sub>p uint (cand + (n + 1))));
           ogets
            (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                    heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                 then 1 else 0)
         })
        (oreturn 0) s = Some ret'"
      using 1(4)
      by (auto simp: obind_def oreturn_def K_def split: option.splits)
    have "?I (n + 1, ret') s"
      by (rule body_preserves_step_pos[OF 1(1) 1(2) 1(3) step])
    thus ?case
      using n'_eq by simp
  qed
  have loop_rule:
    "\<And>init. ?I init s \<Longrightarrow>
      case owhile ?C ?B init s of
        None \<Rightarrow> True
      | Some r \<Rightarrow> ?I r s"
    apply (rule Reader_Monad.owhile_rule[
      where I = ?I
        and M = "measure (\<lambda>(n :: 32 word, ret :: int).
          unat limit - unat n)"])
        apply (simp split: prod.splits)
       apply simp
    subgoal for r r' r''
      by (cases r; cases r'; cases r'')
         (clarsimp intro!: body_decreases unat_suc_measure_decreases)
    subgoal premises prems for r r' r''
    proof (cases r')
      case (Pair n ret)
      note r'_eq = Pair
      show ?thesis
      proof (cases r'')
        case (Pair n' ret')
        note r''_eq = Pair
        have prefix: "\<forall>i < unat n. ?eq i"
          using prems r'_eq by simp
        have n_lt: "unat n < unat limit"
          using prems r'_eq by simp
        have n_eq: "?eq (unat n)"
          using prems r'_eq by simp
        have body:
          "(do {
             ret <-
               ocondition
                (\<lambda>s. n + 1 < limit)
                (do {
                   oguard
                    (\<lambda>st.
                        IS_VALID(8 word) st (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                        IS_VALID(8 word) st (src +\<^sub>p uint (cand + (n + 1))));
                   ogets
                    (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                            heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                         then 1 else 0)
                 })
                (oreturn 0);
             oreturn (n + 1, ret)
           }) s = Some (n', ret')"
          using prems r'_eq r''_eq by simp
        have expanded:
          "unat n' \<le> unat limit \<and>
           (\<forall>i < unat n'. ?eq i) \<and>
           (ret' \<noteq> 0 \<longrightarrow> unat n' < unat limit \<and> ?eq (unat n'))"
          by (rule body_preserves_expanded[OF prefix n_lt n_eq body])
        show ?thesis
          using r''_eq expanded by simp
      qed
    qed
    subgoal for r
      by (cases r) simp
    subgoal for r
      by (cases r) simp
    done
  let ?Init =
    "ocondition
      (\<lambda>s. 0 < limit)
      (do {
         oguard
          (\<lambda>st.
              IS_VALID(8 word) st (tgt +\<^sub>p uint tp) \<and>
              IS_VALID(8 word) st (src +\<^sub>p uint cand));
         ogets
          (\<lambda>s. if heap_w8 s (src +\<^sub>p uint cand) =
                  heap_w8 s (tgt +\<^sub>p uint tp)
               then 1 else 0)
       })
      (oreturn 0)"
  have result_unfolded:
    "(do {
       ret <- ?Init;
       (n, ret) <- owhile ?C ?B (0, ret);
       oreturn n
     }) s = Some l"
  proof -
    have "common_prefix' src cand src_len tgt tp tgt_len s =
      (do {
         ret <- ?Init;
         (n, ret) <- owhile ?C ?B (0, ret);
         oreturn n
       }) s"
      unfolding common_prefix'_def limit_def[symmetric]
      by (simp add: fun_eq_iff split_def)
    thus ?thesis
      using result by simp
  qed
  obtain ret :: int where ret_step: "?Init s = Some ret"
    using result_unfolded
    by (auto simp: obind_def split: option.splits)
  obtain ret_final :: int where loop_res: "owhile ?C ?B (0, ret) s = Some (l, ret_final)"
    using result_unfolded ret_step
    by (auto simp: obind_def oreturn_def K_def split: option.splits prod.splits)
  have init_inv: "?I (0, ret) s"
    using ret_step
    unfolding limit_def
    by (auto simp: ocondition_def obind_def oreturn_def ogets_def oguard_def K_def
                   word_less_nat_alt
             split: if_splits)
  have final_inv: "?I (l, ret_final) s"
    using loop_rule[OF init_inv] loop_res by simp
  thus ?thesis
    by simp
qed

lemma common_prefix'_result_maximal_word:
  fixes src tgt :: "8 word ptr"
    and cand src_len tp tgt_len l :: "32 word"
  assumes result:
    "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
  defines "limit \<equiv>
    (if src_len - cand < tgt_len - tp then src_len - cand else tgt_len - tp)"
  shows "unat l = unat limit \<or>
    heap_w8 s (src +\<^sub>p uint (cand + of_nat (unat l) :: 32 word)) \<noteq>
    heap_w8 s (tgt +\<^sub>p uint (tp + of_nat (unat l) :: 32 word))"
proof -
  let ?eq = "\<lambda>i.
    heap_w8 s (src +\<^sub>p uint (cand + of_nat i :: 32 word)) =
    heap_w8 s (tgt +\<^sub>p uint (tp + of_nat i :: 32 word))"
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
                    (tgt +\<^sub>p uint (tp + (n + 1))) \<and>
                  IS_VALID(8 word) st
                    (src +\<^sub>p uint (cand + (n + 1))));
             ogets
              (\<lambda>s. if heap_w8 s (src +\<^sub>p uint (cand + (n + 1))) =
                      heap_w8 s (tgt +\<^sub>p uint (tp + (n + 1)))
                   then 1 else 0)
           })
          (oreturn 0);
      oreturn (n + 1, ret)
    }"
  let ?I = "\<lambda>(n :: 32 word, ret :: int) s.
    unat n \<le> unat limit \<and>
    (\<forall>i < unat n. ?eq i) \<and>
    (ret \<noteq> 0 \<longleftrightarrow> unat n < unat limit \<and> ?eq (unat n))"
  have body_preserves:
    "\<And>n ret n' ret'. \<lbrakk>?I (n, ret) s; ret \<noteq> 0;
      ?B (n, ret) s = Some (n', ret')\<rbrakk> \<Longrightarrow> ?I (n', ret') s"
  proof -
    fix n n' :: "32 word"
    fix ret ret' :: int
    assume inv: "?I (n, ret) s"
    assume ret_ne: "ret \<noteq> 0"
    assume body: "?B (n, ret) s = Some (n', ret')"
    have n_lt: "unat n < unat limit"
      using inv ret_ne by simp
    have n_word_lt: "n < limit"
      using n_lt by (simp add: word_less_nat_alt)
    have n_suc_unat: "unat (n + 1) = Suc (unat n)"
      by (rule unat_suc_word_less[OF n_word_lt])
    have n'_eq: "n' = n + 1"
      using body
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits)
    have old_eq: "\<And>i. i < unat n \<Longrightarrow> ?eq i"
      using inv by simp
    have n_eq: "?eq (unat n)"
      using inv ret_ne by simp
    have prefix': "\<And>i. i < unat (n + 1) \<Longrightarrow> ?eq i"
    proof -
      fix i
      assume i_lt: "i < unat (n + 1)"
      hence "i < unat n \<or> i = unat n"
        using n_suc_unat by (simp add: less_Suc_eq)
      thus "?eq i"
        using old_eq n_eq by auto
    qed
    have ret'_iff:
      "ret' \<noteq> 0 \<longleftrightarrow> unat (n + 1) < unat limit \<and> ?eq (unat (n + 1))"
      using body
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def word_less_nat_alt add.commute
               split: if_splits)
    show "?I (n', ret') s"
      using n'_eq n_lt n_suc_unat prefix' ret'_iff by (auto simp: add.commute)
  qed
  have body_decreases:
    "\<And>n ret n' ret'. \<lbrakk>?I (n, ret) s; ret \<noteq> 0;
      ?B (n, ret) s = Some (n', ret')\<rbrakk> \<Longrightarrow>
      unat limit - unat n' < unat limit - unat n"
  proof (goal_cases)
    case (1 n ret n' ret')
    have n_lt: "unat n < unat limit"
      using 1(1,2) by simp
    have n_word_lt: "n < limit"
      using n_lt by (simp add: word_less_nat_alt)
    have n_suc_unat: "unat (n + 1) = Suc (unat n)"
      by (rule unat_suc_word_less[OF n_word_lt])
    have n'_eq: "n' = n + 1"
      using 1(3)
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: if_splits)
    have dec: "unat limit - unat (n + 1) < unat limit - unat n"
      using n_lt n_suc_unat by simp
    show ?case
      using dec n'_eq by simp
  qed
  let ?Init =
    "ocondition
      (\<lambda>s. 0 < limit)
      (do {
         oguard
          (\<lambda>st.
              IS_VALID(8 word) st (tgt +\<^sub>p uint tp) \<and>
              IS_VALID(8 word) st (src +\<^sub>p uint cand));
         ogets
          (\<lambda>s. if heap_w8 s (src +\<^sub>p uint cand) =
                  heap_w8 s (tgt +\<^sub>p uint tp)
               then 1 else 0)
       })
      (oreturn 0)"
  have result_unfolded:
    "(do {
       ret <- ?Init;
       (n, ret) <- owhile ?C ?B (0, ret);
       oreturn n
     }) s = Some l"
  proof -
    have "common_prefix' src cand src_len tgt tp tgt_len s =
      (do {
         ret <- ?Init;
         (n, ret) <- owhile ?C ?B (0, ret);
         oreturn n
       }) s"
      unfolding common_prefix'_def limit_def[symmetric]
      by (simp add: fun_eq_iff split_def)
    thus ?thesis
      using result by simp
  qed
  obtain ret :: int where ret_step: "?Init s = Some ret"
    using result_unfolded
    by (auto simp: obind_def split: option.splits)
  obtain ret_final :: int where loop_res:
      "owhile ?C ?B (0, ret) s = Some (l, ret_final)"
    using result_unfolded ret_step
    by (auto simp: obind_def oreturn_def K_def split: option.splits prod.splits)
  have init_inv: "?I (0, ret) s"
    using ret_step
    by (auto simp: ocondition_def obind_def oreturn_def ogets_def oguard_def
                   K_def word_less_nat_alt
             split: if_splits)
  have loop_post:
    "case owhile ?C ?B (0, ret) s of
       None \<Rightarrow> True
     | Some (n, ret') \<Rightarrow> ?I (n, ret') s \<and> ret' = 0"
  proof (rule Reader_Monad.owhile_rule[
      where I = ?I
        and M = "measure (\<lambda>(n :: 32 word, ret :: int).
          unat limit - unat n)"])
    show "?I (0, ret) s"
      by (rule init_inv)
  next
    show "wf (measure (\<lambda>(n :: 32 word, ret :: int).
          unat limit - unat n))"
      by simp
  next
    fix r r' :: "32 word \<times> int"
    assume inv: "?I r s"
      and cond: "?C r s"
      and body: "?B r s = Some r'"
    obtain n ret0 where r_eq: "r = (n, ret0)"
      by (cases r) auto
    obtain n' ret' where r'_eq: "r' = (n', ret')"
      by (cases r') auto
    have inv_pair: "?I (n, ret0) s"
      using inv r_eq by simp
    have cond_pair: "ret0 \<noteq> 0"
      using cond r_eq by simp
    have body_pair: "?B (n, ret0) s = Some (n', ret')"
      using body r_eq r'_eq by simp
    have "unat limit - unat n' < unat limit - unat n"
      by (rule body_decreases[OF inv_pair cond_pair body_pair])
    thus "(r', r) \<in> measure (\<lambda>(n :: 32 word, ret :: int).
          unat limit - unat n)"
      using r_eq r'_eq by simp
  next
    fix r r' :: "32 word \<times> int"
    assume inv: "?I r s"
      and cond: "?C r s"
      and body: "?B r s = Some r'"
    obtain n ret0 where r_eq: "r = (n, ret0)"
      by (cases r) auto
    obtain n' ret' where r'_eq: "r' = (n', ret')"
      by (cases r') auto
    have inv_pair: "?I (n, ret0) s"
      using inv r_eq by simp
    have cond_pair: "ret0 \<noteq> 0"
      using cond r_eq by simp
    have body_pair: "?B (n, ret0) s = Some (n', ret')"
      using body r_eq r'_eq by simp
    have "?I (n', ret') s"
      by (rule body_preserves[OF inv_pair cond_pair body_pair])
    thus "?I r' s"
      using r'_eq by simp
  next
    fix r :: "32 word \<times> int"
    assume "?I r s" "?C r s" "?B r s = None"
    show "case None of None \<Rightarrow> True
      | Some (n, ret') \<Rightarrow> ?I (n, ret') s \<and> ret' = 0"
      by simp
  next
    fix r :: "32 word \<times> int"
    assume inv: "?I r s"
      and exit: "\<not> ?C r s"
    obtain n ret0 where r_eq: "r = (n, ret0)"
      by (cases r) auto
    have ret0_zero: "ret0 = 0"
      using exit r_eq by simp
    show "case Some r of None \<Rightarrow> True
      | Some (n, ret') \<Rightarrow> ?I (n, ret') s \<and> ret' = 0"
      using inv ret0_zero r_eq by simp
  qed
  have post_case:
    "(case Some (l, ret_final) of
       None \<Rightarrow> True
     | Some (n, ret') \<Rightarrow> ?I (n, ret') s \<and> ret' = 0)"
    using loop_post by (simp only: loop_res)
  have post_pair: "?I (l, ret_final) s \<and> ret_final = 0"
    using post_case by auto
  have final_inv: "?I (l, ret_final) s"
    by (rule conjunct1[OF post_pair])
  have ret_final_zero: "ret_final = 0"
    by (rule conjunct2[OF post_pair])
  show ?thesis
  proof (cases "unat l = unat limit")
    case True
    then show ?thesis by simp
  next
    case False
    have l_le: "unat l \<le> unat limit"
      using final_inv by simp
    have "unat l < unat limit"
      using l_le False by linarith
    hence "\<not> ?eq (unat l)"
      using final_inv ret_final_zero by (simp add: word_unat.Rep_inverse)
    then show ?thesis by (simp add: word_unat.Rep_inverse)
  qed
qed

lemma common_prefix'_eq_common_prefix_spec_heap_bytes:
  fixes src tgt :: "8 word ptr"
    and cand src_len tp tgt_len l :: "32 word"
  assumes cp: "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
      and cand_le: "cand \<le> src_len"
      and tp_le: "tp \<le> tgt_len"
  shows "unat l =
    common_prefix_spec
      (heap_bytes s src (unat src_len)) (unat cand) (unat src_len)
      (heap_bytes s tgt (unat tgt_len)) (unat tp) (unat tgt_len)"
proof -
  let ?src_bytes = "heap_bytes s src (unat src_len)"
  let ?tgt_bytes = "heap_bytes s tgt (unat tgt_len)"
  let ?limit =
    "if src_len - cand < tgt_len - tp then src_len - cand else tgt_len - tp"
  let ?fuel = "min (unat src_len - unat cand) (unat tgt_len - unat tp)"
  have limit_nat:
    "unat ?limit = ?fuel"
  proof (cases "src_len - cand < tgt_len - tp")
    case True
    have left: "unat (src_len - cand) = unat src_len - unat cand"
      using cand_le by (simp add: unat_sub word_le_nat_alt)
    have le: "unat (src_len - cand) \<le> unat (tgt_len - tp)"
      using True by (simp add: word_less_nat_alt)
    have right_ge:
      "unat src_len - unat cand \<le> unat tgt_len - unat tp"
      using le left tp_le by (simp add: unat_sub word_le_nat_alt)
    show ?thesis
      using True left right_ge by simp
  next
    case False
    have right: "unat (tgt_len - tp) = unat tgt_len - unat tp"
      using tp_le by (simp add: unat_sub word_le_nat_alt)
    have word_le: "tgt_len - tp \<le> src_len - cand"
      using False by simp
    have le: "unat (tgt_len - tp) \<le> unat (src_len - cand)"
      using word_le by (simp add: word_le_nat_alt)
    have left_ge:
      "unat tgt_len - unat tp \<le> unat src_len - unat cand"
      using le right cand_le by (simp add: unat_sub word_le_nat_alt)
    show ?thesis
      using False right left_ge by simp
  qed
  have sound:
    "unat l \<le> unat ?limit \<and>
     (\<forall>i < unat l.
       heap_w8 s (src +\<^sub>p uint (cand + of_nat i :: 32 word)) =
       heap_w8 s (tgt +\<^sub>p uint (tp + of_nat i :: 32 word)))"
    using common_prefix'_result_sound_word[OF cp] by simp
  have maximal:
    "unat l = unat ?limit \<or>
     heap_w8 s (src +\<^sub>p uint (cand + of_nat (unat l) :: 32 word)) \<noteq>
     heap_w8 s (tgt +\<^sub>p uint (tp + of_nat (unat l) :: 32 word))"
    using common_prefix'_result_maximal_word[OF cp] by simp
  have l_le_fuel: "unat l \<le> ?fuel"
    using sound limit_nat by simp
  have fuel_src: "?fuel \<le> unat src_len - unat cand"
    by simp
  have fuel_tgt: "?fuel \<le> unat tgt_len - unat tp"
    by simp
  have prefix_list:
    "\<And>i. i < unat l \<Longrightarrow>
      unat cand + i < length ?src_bytes \<and>
      unat tp + i < length ?tgt_bytes \<and>
      ?src_bytes ! (unat cand + i) = ?tgt_bytes ! (unat tp + i)"
  proof -
    fix i
    assume i_lt: "i < unat l"
    have src_bound: "unat cand + i < unat src_len"
      using i_lt l_le_fuel fuel_src cand_le
      by (simp add: word_le_nat_alt, linarith)
    have tgt_bound: "unat tp + i < unat tgt_len"
      using i_lt l_le_fuel fuel_tgt tp_le
      by (simp add: word_le_nat_alt, linarith)
    have src_no_overflow: "unat cand + i < 2 ^ 32"
      using src_bound unat_lt2p[of src_len] by simp
    have tgt_no_overflow: "unat tp + i < 2 ^ 32"
      using tgt_bound unat_lt2p[of tgt_len] by simp
    have i_lt32: "i < 2 ^ 32"
      using src_no_overflow by simp
    have of_i_unat: "unat (of_nat i :: 32 word) = i"
      using i_lt32 by (simp add: unat_of_nat_eq)
    have src_idx: "unat (cand + of_nat i :: 32 word) = unat cand + i"
      using src_no_overflow of_i_unat by (simp add: unat_word_ariths)
    have tgt_idx: "unat (tp + of_nat i :: 32 word) = unat tp + i"
      using tgt_no_overflow of_i_unat by (simp add: unat_word_ariths)
    have ptr_eq:
      "heap_w8 s (src +\<^sub>p uint (cand + of_nat i :: 32 word)) =
       heap_w8 s (tgt +\<^sub>p uint (tp + of_nat i :: 32 word))"
      using sound i_lt by blast
    have src_ptr:
      "src +\<^sub>p uint (cand + of_nat i :: 32 word) =
       src +\<^sub>p int (unat cand + i)"
      by (simp only: src_idx uint_nat)
    have tgt_ptr:
      "tgt +\<^sub>p uint (tp + of_nat i :: 32 word) =
       tgt +\<^sub>p int (unat tp + i)"
      by (simp only: tgt_idx uint_nat)
    have src_byte:
      "?src_bytes ! (unat cand + i) =
       heap_w8 s (src +\<^sub>p int (unat cand + i))"
      using src_bound by (simp add: heap_bytes_nth)
    have tgt_byte:
      "?tgt_bytes ! (unat tp + i) =
       heap_w8 s (tgt +\<^sub>p int (unat tp + i))"
      using tgt_bound by (simp add: heap_bytes_nth)
    have byte_eq:
      "?src_bytes ! (unat cand + i) = ?tgt_bytes ! (unat tp + i)"
      using ptr_eq src_ptr tgt_ptr src_byte tgt_byte by simp
    show "unat cand + i < length ?src_bytes \<and>
      unat tp + i < length ?tgt_bytes \<and>
      ?src_bytes ! (unat cand + i) = ?tgt_bytes ! (unat tp + i)"
      using src_bound tgt_bound byte_eq by simp
  qed
  have stop:
    "unat l = ?fuel \<or>
     unat cand + unat l \<ge> length ?src_bytes \<or>
     unat tp + unat l \<ge> length ?tgt_bytes \<or>
     ?src_bytes ! (unat cand + unat l) \<noteq>
     ?tgt_bytes ! (unat tp + unat l)"
  proof (cases "unat l = unat ?limit")
    case True
    then show ?thesis
      using limit_nat by simp
  next
    case False
    have l_lt_limit: "unat l < unat ?limit"
      using sound False by linarith
    have src_bound: "unat cand + unat l < unat src_len"
      using l_lt_limit limit_nat fuel_src cand_le
      by (simp add: word_le_nat_alt, linarith)
    have tgt_bound: "unat tp + unat l < unat tgt_len"
      using l_lt_limit limit_nat fuel_tgt tp_le
      by (simp add: word_le_nat_alt, linarith)
    have src_no_overflow: "unat cand + unat l < 2 ^ 32"
      using src_bound unat_lt2p[of src_len] by simp
    have tgt_no_overflow: "unat tp + unat l < 2 ^ 32"
      using tgt_bound unat_lt2p[of tgt_len] by simp
    have l_lt32: "unat l < 2 ^ 32"
      using src_no_overflow by simp
    have of_l_unat: "unat (of_nat (unat l) :: 32 word) = unat l"
      using l_lt32 by (simp add: unat_of_nat_eq)
    have src_idx:
      "unat (cand + of_nat (unat l) :: 32 word) = unat cand + unat l"
      using src_no_overflow of_l_unat by (simp add: unat_word_ariths)
    have tgt_idx:
      "unat (tp + of_nat (unat l) :: 32 word) = unat tp + unat l"
      using tgt_no_overflow of_l_unat by (simp add: unat_word_ariths)
    have ptr_neq:
      "heap_w8 s (src +\<^sub>p uint (cand + of_nat (unat l) :: 32 word)) \<noteq>
       heap_w8 s (tgt +\<^sub>p uint (tp + of_nat (unat l) :: 32 word))"
      using maximal False by simp
    have src_ptr:
      "src +\<^sub>p uint (cand + of_nat (unat l) :: 32 word) =
       src +\<^sub>p int (unat cand + unat l)"
      by (simp only: src_idx uint_nat)
    have tgt_ptr:
      "tgt +\<^sub>p uint (tp + of_nat (unat l) :: 32 word) =
       tgt +\<^sub>p int (unat tp + unat l)"
      by (simp only: tgt_idx uint_nat)
    have src_byte:
      "?src_bytes ! (unat cand + unat l) =
       heap_w8 s (src +\<^sub>p int (unat cand + unat l))"
      using src_bound by (simp add: heap_bytes_nth)
    have tgt_byte:
      "?tgt_bytes ! (unat tp + unat l) =
       heap_w8 s (tgt +\<^sub>p int (unat tp + unat l))"
      using tgt_bound by (simp add: heap_bytes_nth)
    have byte_neq:
      "?src_bytes ! (unat cand + unat l) \<noteq>
       ?tgt_bytes ! (unat tp + unat l)"
      using ptr_neq src_ptr tgt_ptr src_byte tgt_byte by simp
    show ?thesis
      using byte_neq by simp
  qed
  have fuel_eq:
    "common_prefix_fuel ?fuel ?src_bytes (unat cand) ?tgt_bytes (unat tp) =
     unat l"
    by (rule common_prefix_fuel_eqI[OF l_le_fuel prefix_list stop])
  show ?thesis
    using fuel_eq
    by (simp add: common_prefix_spec_def)
qed

lemma common_prefix'_match_valid_heap_bytes:
  fixes src tgt :: "8 word ptr"
    and cand src_len tp tgt_len l :: "32 word"
  assumes cp: "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
      and cand_le: "cand \<le> src_len"
      and tp_le: "tp \<le> tgt_len"
  shows "match_valid
    (heap_bytes s src (unat src_len))
    (heap_bytes s tgt (unat tgt_len))
    (unat tp) (unat cand) (unat l)"
proof -
  let ?limit =
    "if src_len - cand < tgt_len - tp then src_len - cand else tgt_len - tp"
  have sound:
    "unat l \<le> unat ?limit \<and>
     (\<forall>i < unat l.
       heap_w8 s (src +\<^sub>p uint (cand + of_nat i :: 32 word)) =
       heap_w8 s (tgt +\<^sub>p uint (tp + of_nat i :: 32 word)))"
    using common_prefix'_result_sound_word[OF cp]
    by simp
  have limit_src: "unat ?limit \<le> unat src_len - unat cand"
  proof (cases "src_len - cand < tgt_len - tp")
    case True
    thus ?thesis
      using cand_le by (simp add: unat_sub word_le_nat_alt)
  next
    case False
    hence "tgt_len - tp \<le> src_len - cand"
      by simp
    hence "unat (tgt_len - tp) \<le> unat (src_len - cand)"
      by (simp add: word_le_nat_alt)
    also have "... = unat src_len - unat cand"
      using cand_le by (simp add: unat_sub word_le_nat_alt)
    finally show ?thesis
      using False by simp
  qed
  have limit_tgt: "unat ?limit \<le> unat tgt_len - unat tp"
  proof (cases "src_len - cand < tgt_len - tp")
    case True
    hence "src_len - cand \<le> tgt_len - tp"
      by simp
    hence "unat (src_len - cand) \<le> unat (tgt_len - tp)"
      by (simp add: word_le_nat_alt)
    also have "... = unat tgt_len - unat tp"
      using tp_le by (simp add: unat_sub word_le_nat_alt)
    finally show ?thesis
      using True by simp
  next
    case False
    thus ?thesis
      using tp_le by (simp add: unat_sub word_le_nat_alt)
  qed
  have cand_nat_le: "unat cand \<le> unat src_len"
    using cand_le by (simp add: word_le_nat_alt)
  have tp_nat_le: "unat tp \<le> unat tgt_len"
    using tp_le by (simp add: word_le_nat_alt)
  have l_src_diff: "unat l \<le> unat src_len - unat cand"
    using sound limit_src by linarith
  have l_tgt_diff: "unat l \<le> unat tgt_len - unat tp"
    using sound limit_tgt by linarith
  have src_bound: "unat cand + unat l \<le> unat src_len"
    using cand_nat_le l_src_diff by linarith
  have tgt_bound: "unat tp + unat l \<le> unat tgt_len"
    using tp_nat_le l_tgt_diff by linarith
  have src_no_overflow: "unat cand + unat l < 2 ^ 32"
    using le_less_trans[OF src_bound unat_lt2p[of src_len]] by simp
  have tgt_no_overflow: "unat tp + unat l < 2 ^ 32"
    using le_less_trans[OF tgt_bound unat_lt2p[of tgt_len]] by simp
  show ?thesis
    by (rule match_valid_heap_bytes_wordI[OF src_bound tgt_bound
          src_no_overflow tgt_no_overflow])
       (use sound in auto)
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

lemma match_t_C_eq_enc_matchI:
  assumes pos: "match_t_C.pos_C m = of_nat (em_pos pm)"
      and len: "match_t_C.len_C m = of_nat (em_len pm)"
  shows "m = match_t_C (of_nat (em_pos pm)) (of_nat (em_len pm))"
  using assms
  by (cases m) simp

lemma find_best_match'_early_eq_find_best_match_spec:
  fixes index :: source_index
  assumes early_word: "src_len < 4 \<or> tgt_len - tp < 4"
      and src_len_eq: "length src_bytes = unat src_len"
      and tgt_len_eq: "length tgt_bytes = unat tgt_len"
      and tp_le: "tp \<le> tgt_len"
  shows "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
    Some (match_t_C
      (of_nat (em_pos (find_best_match_spec src_bytes tgt_bytes (unat tp) index)))
      (of_nat (em_len (find_best_match_spec src_bytes tgt_bytes (unat tp) index))))"
proof -
  have early_nat:
    "length src_bytes < min_match \<or>
     length tgt_bytes - unat tp < min_match"
  proof (cases "src_len < 4")
    case True
    then show ?thesis
      using src_len_eq by (simp add: word_less_nat_alt min_match_def)
  next
    case False
    with early_word have tgt_early: "tgt_len - tp < 4"
      by simp
    have "unat (tgt_len - tp) = unat tgt_len - unat tp"
      using tp_le by (simp add: unat_sub word_le_nat_alt)
    with tgt_early show ?thesis
      using tgt_len_eq by (simp add: word_less_nat_alt min_match_def)
  qed
  have spec_no:
    "find_best_match_spec src_bytes tgt_bytes (unat tp) index = no_match"
    using early_nat
    by (simp add: find_best_match_spec_def no_match_def)
  show ?thesis
    using find_best_match'_early_zero[OF early_word]
    by (simp add: spec_no no_match_def)
qed

lemma find_best_match'_not_early_src_bound:
  fixes src_len tgt_len tp :: "32 word"
  assumes not_early: "\<not> (src_len < (4 :: 32 word) \<or> tgt_len - tp < 4)"
  shows "min_match \<le> unat src_len"
  using not_early
  by (simp add: min_match_def word_less_nat_alt)

lemma find_best_match'_not_early_tgt_bound:
  fixes src_len tgt_len tp :: "32 word"
  assumes tp_le: "tp \<le> tgt_len"
      and not_early: "\<not> (src_len < (4 :: 32 word) \<or> tgt_len - tp < 4)"
  shows "unat tp + min_match \<le> unat tgt_len"
proof -
  have not_lt: "\<not> (tgt_len - tp < (4 :: 32 word))"
    using not_early by simp
  have "unat (4 :: 32 word) \<le> unat (tgt_len - tp)"
    using not_lt by (simp add: word_less_nat_alt not_less)
  hence "4 \<le> unat (tgt_len - tp)"
    by simp
  also have "\<dots> = unat tgt_len - unat tp"
    using tp_le by (simp add: unat_sub word_le_nat_alt)
  finally show ?thesis
    by (simp add: min_match_def)
qed

lemma find_best_match'_target_hash_bucket:
  fixes tgt :: "8 word ptr"
    and src_len tgt_len tp hv :: "32 word"
  assumes tp_le: "tp \<le> tgt_len"
      and not_early: "\<not> (src_len < (4 :: 32 word) \<or> tgt_len - tp < 4)"
      and tgt_ok: "buf_valid s tgt (unat tgt_len)"
      and hash_res: "hash4' tgt tp s = Some hv"
  shows "hv && 0xFFFF =
    (of_nat (hash_bucket_spec (heap_bytes s tgt (unat tgt_len)) (unat tp))
      :: 32 word)"
proof -
  have len: "unat tp + min_match \<le> unat tgt_len"
    by (rule find_best_match'_not_early_tgt_bound[OF tp_le not_early])
  have hash_eq:
    "hash4' tgt tp s =
      Some (of_nat
        (hash4_spec (heap_bytes s tgt (unat tgt_len)) (unat tp)) :: 32 word)"
    by (rule hash4'_heap_bytes_buf_valid[OF len tgt_ok])
  hence hv_eq:
    "hv =
      (of_nat
        (hash4_spec (heap_bytes s tgt (unat tgt_len)) (unat tp)) :: 32 word)"
    using hash_res by simp
  show ?thesis
    using hv_eq by (simp add: hash_bucket_word_from_hash4_spec)
qed

definition enc_match_of_words :: "32 word \<Rightarrow> 32 word \<Rightarrow> enc_match" where
  "enc_match_of_words best_len best_pos =
     \<lparr>em_pos = unat best_pos, em_len = unat best_len\<rparr>"

lemma find_best_match_spec_non_early_build_index:
  assumes src_not_early: "min_match \<le> length src_bytes"
      and tgt_not_early: "unat tp + min_match \<le> length tgt_bytes"
  shows "find_best_match_spec src_bytes tgt_bytes (unat tp)
      (build_index_spec src_bytes) =
    foldl (\<lambda>best cand. choose_match_spec src_bytes tgt_bytes (unat tp) cand best)
      no_match
      (take max_chain
        (index_bucket_spec (build_index_spec src_bytes)
          (hash_bucket_spec tgt_bytes (unat tp))))"
proof -
  have tgt_len_not_early: "min_match \<le> length tgt_bytes - unat tp"
    using tgt_not_early by simp
  show ?thesis
    using src_not_early tgt_len_not_early
    by (simp add: find_best_match_spec_def Let_def)
qed

lemma match_candidate_word_guard:
  fixes cand src_len :: "32 word"
  assumes cand_match: "unat cand + min_match \<le> unat src_len"
  shows "cand + 4 \<le> src_len"
proof -
  have cand_4_le: "unat cand + 4 \<le> unat src_len"
    using cand_match by (simp add: min_match_def)
  have no_overflow: "unat cand + unat (4 :: 32 word) < 2 ^ 32"
    using cand_4_le unat_lt2p[of src_len] by simp
  have unat_add: "unat (cand + 4) = unat cand + 4"
    using no_overflow by (simp add: unat_word_ariths(1))
  show ?thesis
    using cand_4_le by (simp add: word_le_nat_alt unat_add)
qed

lemma choose_match_spec_heap_word:
  fixes src tgt :: "8 word ptr"
    and best_len best_pos cand l src_len tp tgt_len :: "32 word"
    and s :: lifted_globals
  defines "src_bytes \<equiv> heap_bytes s src (unat src_len)"
  defines "tgt_bytes \<equiv> heap_bytes s tgt (unat tgt_len)"
  defines "best \<equiv> \<lparr>em_pos = unat best_pos, em_len = unat best_len\<rparr>"
  assumes cp: "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
      and cand_match: "unat cand + min_match \<le> length src_bytes"
      and cand_le: "cand \<le> src_len"
      and tp_le: "tp \<le> tgt_len"
  shows "choose_match_spec src_bytes tgt_bytes (unat tp) (unat cand) best =
    (if 4 \<le> l \<and> best_len < l
     then \<lparr>em_pos = unat cand, em_len = unat l\<rparr>
     else best)"
proof -
  have cp_eq:
    "common_prefix_spec src_bytes (unat cand) (length src_bytes)
       tgt_bytes (unat tp) (length tgt_bytes) = unat l"
    using common_prefix'_eq_common_prefix_spec_heap_bytes[
        OF cp cand_le tp_le]
    by (simp add: src_bytes_def tgt_bytes_def)
  have min_l_iff: "(min_match \<le> unat l) \<longleftrightarrow> 4 \<le> l"
    by (simp add: min_match_def word_le_nat_alt)
  have best_l_iff: "(em_len best < unat l) \<longleftrightarrow> best_len < l"
    by (simp add: best_def word_less_nat_alt)
  show ?thesis
    using cand_match cp_eq min_l_iff best_l_iff
    by (simp add: choose_match_spec_def best_def Let_def)
qed

lemma enc_match_of_words_update_choose_match:
  fixes src tgt :: "8 word ptr"
    and best_len best_pos cand l src_len tp tgt_len :: "32 word"
    and s :: lifted_globals
  assumes cp: "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
      and cand_match:
        "unat cand + min_match \<le> length (heap_bytes s src (unat src_len))"
      and cand_le: "cand \<le> src_len"
      and tp_le: "tp \<le> tgt_len"
  shows "enc_match_of_words
      (if 4 \<le> l \<and> best_len < l then l else best_len)
      (if 4 \<le> l \<and> best_len < l then cand else best_pos) =
    choose_match_spec
      (heap_bytes s src (unat src_len))
      (heap_bytes s tgt (unat tgt_len))
      (unat tp) (unat cand)
      (enc_match_of_words best_len best_pos)"
proof -
  have choose:
    "choose_match_spec
      (heap_bytes s src (unat src_len))
      (heap_bytes s tgt (unat tgt_len))
      (unat tp) (unat cand)
      (enc_match_of_words best_len best_pos) =
    (if 4 \<le> l \<and> best_len < l
     then \<lparr>em_pos = unat cand, em_len = unat l\<rparr>
     else enc_match_of_words best_len best_pos)"
    unfolding enc_match_of_words_def
    by (rule choose_match_spec_heap_word[
        OF cp cand_match cand_le tp_le])
  show ?thesis
    using choose by (simp add: enc_match_of_words_def)
qed

lemma match_t_C_sel_simps:
  "match_t_C.pos_C (match_t_C pos len) = pos"
  "match_t_C.len_C (match_t_C pos len) = len"
  by simp_all

lemma find_best_match'_nonearly_obtain_loop:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len tp :: "32 word"
  assumes not_early: "\<not> (src_len < 4 \<or> tgt_len - tp < 4)"
      and result:
        "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m"
  obtains hv best_len best_pos cand checked :: "32 word"
    where "hash4' tgt tp s = Some hv"
      and "owhile
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
             cand :: 32 word, checked :: 32 word) s.
              cand \<noteq> no_entry32 \<and> checked < (0x10 :: 32 word))
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
             cand :: 32 word, checked :: 32 word) s.
              case if cand + 4 \<le> src_len
                   then case common_prefix' src cand src_len tgt tp tgt_len s of
                     None \<Rightarrow> None
                   | Some l \<Rightarrow>
                       Some (if 4 \<le> l \<and> best_len < l
                         then (l, cand) else (best_len, best_pos))
                   else Some (best_len, best_pos) of
                None \<Rightarrow> None
              | Some p \<Rightarrow>
                  (case p of
                   (best_len, best_pos) \<Rightarrow>
                     \<lambda>s. case if IS_VALID(32 word) s
                         (next_arr +\<^sub>p uint cand)
                       then Some () else None of
                         None \<Rightarrow> None
                       | Some _ \<Rightarrow>
                           Some (best_len, best_pos,
                             heap_w32 s (next_arr +\<^sub>p uint cand),
                             checked + (1 :: 32 word)))
                  s)
          ((0 :: 32 word), (0 :: 32 word),
            heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)),
            (0 :: 32 word)) s =
         Some (best_len, best_pos, cand, checked)"
      and "m = match_t_C best_pos best_len"
  using result not_early
  unfolding find_best_match'_def
  by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                 oguard_def K_def
           split: option.splits prod.splits if_splits)

lemma find_best_match'_nonearly_eq_find_best_match_spec:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len tp :: "32 word"
  assumes rel:
    "source_index_heap_rel s (heap_bytes s src (unat src_len)) head_arr next_arr"
      and closed:
    "source_index_heap_chains_closed s (heap_bytes s src (unat src_len)) head_arr next_arr"
      and nexts_wf:
    "source_index_heap_nexts_wf s (heap_bytes s src (unat src_len)) next_arr"
      and tp_le: "tp \<le> tgt_len"
      and tgt_ok: "buf_valid s tgt (unat tgt_len)"
      and not_early: "\<not> (src_len < 4 \<or> tgt_len - tp < 4)"
      and result:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m"
  shows "m = match_t_C
    (of_nat (em_pos (find_best_match_spec
      (heap_bytes s src (unat src_len))
      (heap_bytes s tgt (unat tgt_len)) (unat tp)
      (build_index_spec (heap_bytes s src (unat src_len))))))
    (of_nat (em_len (find_best_match_spec
      (heap_bytes s src (unat src_len))
      (heap_bytes s tgt (unat tgt_len)) (unat tp)
      (build_index_spec (heap_bytes s src (unat src_len))))))"
proof -
  let ?src_bytes = "heap_bytes s src (unat src_len)"
  let ?tgt_bytes = "heap_bytes s tgt (unat tgt_len)"
  let ?nexts = "heap_w32_list s next_arr (length ?src_bytes)"
  let ?cand_ok = "\<lambda>cand :: 32 word.
    cand = no_entry32 \<or> unat cand + min_match \<le> length ?src_bytes"
  let ?step = "\<lambda>best cand.
    choose_match_spec ?src_bytes ?tgt_bytes (unat tp) cand best"
  let ?C = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word) s.
      cand \<noteq> no_entry32 \<and> checked < 0x10"
  let ?Update = "\<lambda>(best_len :: 32 word) (best_pos :: 32 word)
                    (cand :: 32 word).
      ocondition (\<lambda>s. cand + 4 \<le> src_len)
        (do {
          l <- common_prefix' src cand src_len tgt tp tgt_len;
          oreturn
            (if 4 \<le> l \<and> best_len < l then (l, cand)
             else (best_len, best_pos))
        })
        (oreturn (best_len, best_pos))"
  let ?After = "\<lambda>(cand :: 32 word) (checked :: 32 word)
                  (best_len :: 32 word, best_pos :: 32 word).
      do {
        oguard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint cand));
        ogets
          (\<lambda>s. (best_len, best_pos,
                heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1))
      }"
  let ?B = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word).
      do {
        p <- ?Update best_len best_pos cand;
        ?After cand checked p
      }"
  have src_not_early: "min_match \<le> length ?src_bytes"
    using find_best_match'_not_early_src_bound[OF not_early] by simp
  have tgt_not_early: "unat tp + min_match \<le> length ?tgt_bytes"
    using find_best_match'_not_early_tgt_bound[OF tp_le not_early] by simp
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
  have body_preserves:
    "\<And>cand0 best_len best_pos cand checked best_len' best_pos' cand' checked'.
      \<lbrakk>
        enc_match_of_words best_len best_pos =
          foldl ?step no_match (match_word_chain ?nexts (unat checked) cand0);
        cand = match_word_cursor ?nexts (unat checked) cand0;
        unat checked \<le> max_chain;
        ?cand_ok cand;
        cand \<noteq> no_entry32;
        checked < 0x10;
        ?B (best_len, best_pos, cand, checked) s =
          Some (best_len', best_pos', cand', checked')\<rbrakk>
      \<Longrightarrow>
        enc_match_of_words best_len' best_pos' =
          foldl ?step no_match (match_word_chain ?nexts (unat checked') cand0) \<and>
        cand' = match_word_cursor ?nexts (unat checked') cand0 \<and>
        unat checked' \<le> max_chain \<and>
        ?cand_ok cand'"
  proof -
    fix cand0 best_len best_pos cand checked best_len' best_pos' cand' checked' :: "32 word"
    assume best_inv:
      "enc_match_of_words best_len best_pos =
        foldl ?step no_match (match_word_chain ?nexts (unat checked) cand0)"
    assume cand_inv:
      "cand = match_word_cursor ?nexts (unat checked) cand0"
    assume checked_le: "unat checked \<le> max_chain"
    assume cand_ok: "?cand_ok cand"
    assume cand_not_noentry: "cand \<noteq> no_entry32"
    assume checked_lt_word: "checked < 0x10"
    assume body:
      "?B (best_len, best_pos, cand, checked) s =
        Some (best_len', best_pos', cand', checked')"
    have checked_lt: "unat checked < max_chain"
      using checked_lt_word by (simp add: max_chain_def word_less_nat_alt)
    have checked_suc: "unat (checked + 1) = Suc (unat checked)"
      by (rule unat_suc_word_less[OF checked_lt_word])
    have checked'_le: "unat (checked + 1) \<le> max_chain"
      using checked_lt checked_suc by simp
    have cand_match: "unat cand + min_match \<le> length ?src_bytes"
      using cand_ok cand_not_noentry by simp
    have cand_lt_nexts: "unat cand < length ?nexts"
      using cand_match by (simp add: min_match_def)
    have cand_le_src: "cand \<le> src_len"
      using cand_match by (simp add: word_le_nat_alt)
    have cand_guard: "cand + 4 \<le> src_len"
      by (rule match_candidate_word_guard) (use cand_match in simp)
    have body_obind:
      "obind (?Update best_len best_pos cand) (?After cand checked) s =
        Some (best_len', best_pos', cand', checked')"
      using body by simp
    obtain upd where upd_res0: "?Update best_len best_pos cand s = Some upd"
      and after_res: "?After cand checked upd s =
        Some (best_len', best_pos', cand', checked')"
      using reader_obind_SomeE[OF body_obind] by blast
    obtain upd_len upd_pos where upd_eq: "upd = (upd_len, upd_pos)"
      by (cases upd) auto
    have upd_do:
      "(do {
         l <- common_prefix' src cand src_len tgt tp tgt_len;
         oreturn
           (if 4 \<le> l \<and> best_len < l then (l, cand)
            else (best_len, best_pos))
       }) s = Some (upd_len, upd_pos)"
      using upd_res0 upd_eq cand_guard
      by (simp add: ocondition_def)
    obtain l where cp:
      "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
      and upd_pair:
      "(upd_len, upd_pos) =
        (if 4 \<le> l \<and> best_len < l then (l, cand)
         else (best_len, best_pos))"
    proof (cases "common_prefix' src cand src_len tgt tp tgt_len s")
      case None
      thus ?thesis
        using upd_do by (simp add: obind_def)
    next
      case (Some l)
      have "(upd_len, upd_pos) =
        (if 4 \<le> l \<and> best_len < l then (l, cand)
         else (best_len, best_pos))"
        using upd_do Some by (simp add: obind_def oreturn_def K_def)
      thus ?thesis
        using Some that by blast
    qed
    let ?valid_next = "IS_VALID(32 word) s (next_arr +\<^sub>p uint cand)"
    have after_res_pair:
      "?After cand checked (upd_len, upd_pos) s =
        Some (best_len', best_pos', cand', checked')"
      using after_res upd_eq by simp
    have after_unfold:
      "?After cand checked (upd_len, upd_pos) s =
        (if ?valid_next
         then Some (upd_len, upd_pos,
           heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1)
         else None)"
      by (simp add: obind_def oguard_def ogets_def K_def)
    have after_tuple_eq:
      "(upd_len, upd_pos, heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1) =
       (best_len', best_pos', cand', checked')"
      using after_res_pair after_unfold
      by (cases ?valid_next) simp_all
    have best_len'_eq: "best_len' = upd_len"
      and best_pos'_eq: "best_pos' = upd_pos"
      and cand'_eq: "cand' = heap_w32 s (next_arr +\<^sub>p uint cand)"
      and checked'_eq: "checked' = checked + 1"
      using after_tuple_eq by simp_all
    have upd_len_eq:
      "upd_len = (if 4 \<le> l \<and> best_len < l then l else best_len)"
      using arg_cong[OF upd_pair, where f=fst] by simp
    have upd_pos_eq:
      "upd_pos = (if 4 \<le> l \<and> best_len < l then cand else best_pos)"
      using arg_cong[OF upd_pair, where f=snd] by simp
    have upd_choose:
      "enc_match_of_words upd_len upd_pos =
        ?step (enc_match_of_words best_len best_pos) (unat cand)"
      using enc_match_of_words_update_choose_match[
          OF cp cand_match cand_le_src tp_le] upd_len_eq upd_pos_eq
      by simp
    have chain_suc:
      "match_word_chain ?nexts (Suc (unat checked)) cand0 =
       match_word_chain ?nexts (unat checked) cand0 @ [unat cand]"
      by (rule match_word_chain_Suc_cursor[
          OF cand_inv[symmetric] cand_not_noentry cand_lt_nexts])
    have cursor_suc:
      "match_word_cursor ?nexts (Suc (unat checked)) cand0 =
       ?nexts ! unat cand"
      by (rule match_word_cursor_Suc_step[
          OF cand_inv[symmetric] cand_not_noentry cand_lt_nexts])
    have cand_lt_src_bytes: "unat cand < length ?src_bytes"
      using cand_lt_nexts by simp
    have next_read_int:
      "?nexts ! unat cand = heap_w32 s (next_arr +\<^sub>p int (unat cand))"
      by (rule heap_w32_list_nth[OF cand_lt_src_bytes])
    have next_read:
      "heap_w32 s (next_arr +\<^sub>p uint cand) = ?nexts ! unat cand"
      using next_read_int by (simp only: uint_nat)
    have best':
      "enc_match_of_words best_len' best_pos' =
        foldl ?step no_match
          (match_word_chain ?nexts (unat checked') cand0)"
      using best_inv upd_choose chain_suc checked_suc checked'_eq
        best_len'_eq best_pos'_eq
      by simp
    have cursor':
      "cand' = match_word_cursor ?nexts (unat checked') cand0"
      using cand'_eq checked'_eq checked_suc cursor_suc next_read by simp
    have cand_ok': "?cand_ok cand'"
      using cand'_eq next_cand_ok[OF cand_ok cand_not_noentry] by simp
    show "enc_match_of_words best_len' best_pos' =
          foldl ?step no_match (match_word_chain ?nexts (unat checked') cand0) \<and>
        cand' = match_word_cursor ?nexts (unat checked') cand0 \<and>
        unat checked' \<le> max_chain \<and> ?cand_ok cand'"
      using best' cursor' checked'_eq checked'_le cand_ok' by simp
  qed
  have body_decreases:
    "\<And>best_len best_pos cand checked best_len' best_pos' cand' checked'.
      \<lbrakk>checked < 0x10;
        ?B (best_len, best_pos, cand, checked) s =
          Some (best_len', best_pos', cand', checked')\<rbrakk>
      \<Longrightarrow> 16 - unat checked' < 16 - unat checked"
  proof -
    fix best_len best_pos cand checked best_len' best_pos' cand' checked' :: "32 word"
    assume checked_lt: "checked < 0x10"
    assume body:
      "?B (best_len, best_pos, cand, checked) s =
        Some (best_len', best_pos', cand', checked')"
    have body_obind:
      "obind (?Update best_len best_pos cand) (?After cand checked) s =
        Some (best_len', best_pos', cand', checked')"
      using body by simp
    obtain upd where after_res:
      "?After cand checked upd s = Some (best_len', best_pos', cand', checked')"
      using reader_obind_SomeE[OF body_obind] by blast
    obtain upd_len upd_pos where upd_eq: "upd = (upd_len, upd_pos)"
      by (cases upd) auto
    let ?valid_next = "IS_VALID(32 word) s (next_arr +\<^sub>p uint cand)"
    have after_res_pair:
      "?After cand checked (upd_len, upd_pos) s =
        Some (best_len', best_pos', cand', checked')"
      using after_res upd_eq by simp
    have after_unfold:
      "?After cand checked (upd_len, upd_pos) s =
        (if ?valid_next
         then Some (upd_len, upd_pos,
           heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1)
         else None)"
      by (simp add: obind_def oguard_def ogets_def K_def)
    have after_tuple_eq:
      "(upd_len, upd_pos, heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1) =
       (best_len', best_pos', cand', checked')"
      using after_res_pair after_unfold
      by (cases ?valid_next) simp_all
    have checked'_eq: "checked' = checked + 1"
      using after_tuple_eq by simp
    show "16 - unat checked' < 16 - unat checked"
      using checked_measure_decreases[OF checked_lt] checked'_eq by simp
  qed
  obtain hv best_len best_pos cand checked :: "32 word" where
      hash_res: "hash4' tgt tp s = Some hv"
    and ow:
      "owhile ?C ?B
        (0, 0, heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)), 0) s =
       Some (best_len, best_pos, cand, checked)"
    and m_eq: "m = match_t_C best_pos best_len"
  proof (rule find_best_match'_nonearly_obtain_loop[
      OF not_early result])
    fix hv best_len best_pos cand checked :: "32 word"
    assume hash: "hash4' tgt tp s = Some hv"
    assume loop:
      "owhile
        (\<lambda>(best_len, best_pos, cand, checked) s.
            cand \<noteq> no_entry32 \<and> checked < 0x10)
        (\<lambda>(best_len, best_pos, cand, checked) s.
            case if cand + 4 \<le> src_len
                 then case common_prefix' src cand src_len tgt tp tgt_len s of
                   None \<Rightarrow> None
                 | Some l \<Rightarrow>
                     Some (if 4 \<le> l \<and> best_len < l
                       then (l, cand) else (best_len, best_pos))
                 else Some (best_len, best_pos) of
              None \<Rightarrow> None
            | Some p \<Rightarrow>
                (case p of
                 (best_len, best_pos) \<Rightarrow>
                   \<lambda>s. case if IS_VALID(32 word) s
                       (next_arr +\<^sub>p uint cand)
                     then Some () else None of
                       None \<Rightarrow> None
                     | Some _ \<Rightarrow>
                         Some (best_len, best_pos,
                           heap_w32 s (next_arr +\<^sub>p uint cand),
                           checked + 1)) s)
        (0, 0, heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)), 0) s =
       Some (best_len, best_pos, cand, checked)"
    assume m: "m = match_t_C best_pos best_len"
    have loop_abbrev:
      "owhile ?C ?B
        (0, 0, heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)), 0) s =
       Some (best_len, best_pos, cand, checked)"
      using loop
      by (simp add: obind_def ocondition_def oreturn_def ogets_def
                    oguard_def K_def
              split: option.splits prod.splits if_splits)
    show ?thesis
      using that[OF hash loop_abbrev m] .
  qed
  let ?h = "hash_bucket_spec ?tgt_bytes (unat tp)"
  let ?cand0 = "heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF))"
  have h_lt: "?h < hash_size"
    by (rule hash_bucket_spec_lt)
  have hv_bucket:
    "hv && 0xFFFF = (of_nat ?h :: 32 word)"
    by (rule find_best_match'_target_hash_bucket[
        OF tp_le not_early tgt_ok hash_res])
  have hv_bucket_unat: "unat (hv && 0xFFFF) = ?h"
    using hv_bucket h_lt by (simp add: unat_of_nat_eq hash_size_def hash_bits_def)
  have cand0_int:
    "?cand0 = heap_w32 s (head_arr +\<^sub>p int ?h)"
    by (simp only: hv_bucket_unat uint_nat)
  have cand0_ok: "?cand_ok ?cand0"
    using initial_cand_ok[of hv] by simp
  have chain_candidates:
    "match_word_chain ?nexts max_chain ?cand0 =
     take max_chain (index_bucket_spec (build_index_spec ?src_bytes) ?h)"
    using source_index_heap_chains_closed_max_chain_candidates[
        OF closed h_lt]
    by (simp only: cand0_int)
  let ?I = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word) s.
      enc_match_of_words best_len best_pos =
        foldl ?step no_match (match_word_chain ?nexts (unat checked) ?cand0) \<and>
      cand = match_word_cursor ?nexts (unat checked) ?cand0 \<and>
      unat checked \<le> max_chain \<and>
      ?cand_ok cand"
  have loop_post:
    "case owhile ?C ?B (0, 0, ?cand0, 0) s of
       None \<Rightarrow> True
     | Some (best_len, best_pos, cand, checked) \<Rightarrow>
        ?I (best_len, best_pos, cand, checked) s \<and> \<not> ?C (best_len, best_pos, cand, checked) s"
  proof (rule Reader_Monad.owhile_rule[
      where I = ?I
        and M = "measure
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
               cand :: 32 word, checked :: 32 word). 16 - unat checked)"])
    show "?I (0, 0, ?cand0, 0) s"
      using cand0_ok by (simp add: enc_match_of_words_def no_match_def max_chain_def)
  next
    show "wf (measure
      (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
          cand :: 32 word, checked :: 32 word). 16 - unat checked))"
      by simp
  next
    fix r r' :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    assume inv: "?I r s"
      and cond: "?C r s"
      and body: "?B r s = Some r'"
    obtain best_len best_pos cand checked where r_eq:
      "r = (best_len, best_pos, cand, checked)"
      by (cases r) auto
    obtain best_len' best_pos' cand' checked' where r'_eq:
      "r' = (best_len', best_pos', cand', checked')"
      by (cases r') auto
    have "16 - unat checked' < 16 - unat checked"
      by (rule body_decreases)
         (use cond body r_eq r'_eq in simp_all)
    thus "(r', r) \<in> measure
        (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
            cand :: 32 word, checked :: 32 word). 16 - unat checked)"
      using r_eq r'_eq by simp
  next
    fix r r' :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    assume inv: "?I r s"
      and cond: "?C r s"
      and body: "?B r s = Some r'"
    obtain best_len best_pos cand checked where r_eq:
      "r = (best_len, best_pos, cand, checked)"
      by (cases r) auto
    obtain best_len' best_pos' cand' checked' where r'_eq:
      "r' = (best_len', best_pos', cand', checked')"
      by (cases r') auto
    have inv_tuple: "?I (best_len, best_pos, cand, checked) s"
      using inv by (simp only: r_eq[symmetric])
    have cond_tuple: "?C (best_len, best_pos, cand, checked) s"
      using cond by (simp only: r_eq[symmetric])
    have best_inv_t:
      "enc_match_of_words best_len best_pos =
        foldl ?step no_match (match_word_chain ?nexts (unat checked) ?cand0)"
      using inv_tuple by simp
    have cand_inv_t:
      "cand = match_word_cursor ?nexts (unat checked) ?cand0"
      using inv_tuple by simp
    have checked_le_t: "unat checked \<le> max_chain"
      using inv_tuple by simp
    have cand_ok_t: "?cand_ok cand"
      using inv_tuple by blast
    have cand_not_noentry_t: "cand \<noteq> no_entry32"
      using cond_tuple by simp
    have checked_lt_word_t: "checked < 0x10"
      using cond_tuple by simp
    have body_tuple:
      "?B (best_len, best_pos, cand, checked) s =
        Some (best_len', best_pos', cand', checked')"
      using body by (simp only: r_eq[symmetric] r'_eq[symmetric])
    have preserved:
      "enc_match_of_words best_len' best_pos' =
          foldl ?step no_match (match_word_chain ?nexts (unat checked') ?cand0) \<and>
        cand' = match_word_cursor ?nexts (unat checked') ?cand0 \<and>
        unat checked' \<le> max_chain \<and> ?cand_ok cand'"
      by (rule body_preserves[
          OF best_inv_t cand_inv_t checked_le_t cand_ok_t
             cand_not_noentry_t checked_lt_word_t body_tuple])
    have preserved_tuple: "?I (best_len', best_pos', cand', checked') s"
      using preserved by blast
    show "?I r' s"
      using preserved_tuple by (simp only: r'_eq[symmetric])
  next
    fix r :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    assume "?I r s" "?C r s" "?B r s = None"
    show "case None of None \<Rightarrow> True
      | Some (best_len, best_pos, cand, checked) \<Rightarrow>
          ?I (best_len, best_pos, cand, checked) s \<and>
          \<not> ?C (best_len, best_pos, cand, checked) s"
      by simp
  next
    fix r :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    assume inv: "?I r s"
      and exit: "\<not> ?C r s"
    show "case Some r of None \<Rightarrow> True
      | Some (best_len, best_pos, cand, checked) \<Rightarrow>
          ?I (best_len, best_pos, cand, checked) s \<and>
          \<not> ?C (best_len, best_pos, cand, checked) s"
      using inv exit by (cases r) simp
  qed
  have final_post_case:
    "case Some (best_len, best_pos, cand, checked) of
       None \<Rightarrow> True
     | Some (bl, bp, ca, ch) \<Rightarrow>
        ?I (bl, bp, ca, ch) s \<and> \<not> ?C (bl, bp, ca, ch) s"
    using loop_post by (simp only: ow)
  have final_post:
    "?I (best_len, best_pos, cand, checked) s \<and>
     \<not> ?C (best_len, best_pos, cand, checked) s"
    using final_post_case by (simp (no_asm_use) only: option.case prod.case)
  have final_inv:
    "enc_match_of_words best_len best_pos =
      foldl ?step no_match (match_word_chain ?nexts (unat checked) ?cand0)"
    using final_post by simp
  have final_cursor:
    "cand = match_word_cursor ?nexts (unat checked) ?cand0"
    using final_post by simp
  have final_checked_le:
    "unat checked \<le> max_chain"
    using final_post by simp
  have final_exit:
    "cand = no_entry32 \<or> unat checked = max_chain"
  proof -
    have notC: "\<not> ?C (best_len, best_pos, cand, checked) s"
      using final_post by (rule conjunct2)
    have exit: "\<not> (cand \<noteq> no_entry32 \<and> checked < (0x10 :: 32 word))"
      using notC by simp
    show ?thesis
    proof (cases "cand = no_entry32")
      case True
      then show ?thesis by simp
    next
      case False
      with exit have "\<not> checked < (0x10 :: 32 word)"
        by simp
      hence "max_chain \<le> unat checked"
        by (simp add: max_chain_def word_less_nat_alt not_less)
      with final_checked_le show ?thesis
        by simp
    qed
  qed
  have chain_final:
    "match_word_chain ?nexts max_chain ?cand0 =
     match_word_chain ?nexts (unat checked) ?cand0"
    by (rule match_word_chain_exit_prefix_max_chain[
        OF final_checked_le final_cursor[symmetric] final_exit])
  have best_eq_candidates:
    "enc_match_of_words best_len best_pos =
      foldl ?step no_match
        (take max_chain
          (index_bucket_spec (build_index_spec ?src_bytes) ?h))"
    using final_inv chain_final chain_candidates by simp
  have spec_eq:
    "find_best_match_spec ?src_bytes ?tgt_bytes (unat tp)
      (build_index_spec ?src_bytes) =
      foldl ?step no_match
        (take max_chain
          (index_bucket_spec (build_index_spec ?src_bytes) ?h))"
    by (rule find_best_match_spec_non_early_build_index[
        OF src_not_early tgt_not_early])
  let ?spec =
    "find_best_match_spec ?src_bytes ?tgt_bytes (unat tp)
      (build_index_spec ?src_bytes)"
  have best_spec:
    "enc_match_of_words best_len best_pos = ?spec"
    using best_eq_candidates spec_eq by simp
  have pos_nat_eq: "em_pos ?spec = unat best_pos"
    using arg_cong[OF best_spec, where f=em_pos]
    by (simp add: enc_match_of_words_def)
  have len_nat_eq: "em_len ?spec = unat best_len"
    using arg_cong[OF best_spec, where f=em_len]
    by (simp add: enc_match_of_words_def)
  have pos_eq:
    "best_pos = of_nat (em_pos ?spec)"
    using pos_nat_eq by (simp add: word_unat.Rep_inverse)
  have len_eq:
    "best_len = of_nat (em_len ?spec)"
    using len_nat_eq by (simp add: word_unat.Rep_inverse)
  show ?thesis
    using m_eq pos_eq len_eq by simp
qed

lemma find_best_match'_eq_find_best_match_spec:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len tp :: "32 word"
  assumes rel:
    "source_index_heap_rel s (heap_bytes s src (unat src_len)) head_arr next_arr"
      and closed:
    "source_index_heap_chains_closed s (heap_bytes s src (unat src_len)) head_arr next_arr"
      and nexts_wf:
    "source_index_heap_nexts_wf s (heap_bytes s src (unat src_len)) next_arr"
      and tp_le: "tp \<le> tgt_len"
      and tgt_ok: "buf_valid s tgt (unat tgt_len)"
      and result:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m"
  shows "m = match_t_C
    (of_nat (em_pos (find_best_match_spec
      (heap_bytes s src (unat src_len))
      (heap_bytes s tgt (unat tgt_len)) (unat tp)
      (build_index_spec (heap_bytes s src (unat src_len))))))
    (of_nat (em_len (find_best_match_spec
      (heap_bytes s src (unat src_len))
      (heap_bytes s tgt (unat tgt_len)) (unat tp)
      (build_index_spec (heap_bytes s src (unat src_len))))))"
proof (cases "src_len < 4 \<or> tgt_len - tp < 4")
  case True
  let ?src_bytes = "heap_bytes s src (unat src_len)"
  let ?tgt_bytes = "heap_bytes s tgt (unat tgt_len)"
  have f_eq:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s =
      Some (match_t_C
        (of_nat (em_pos (find_best_match_spec ?src_bytes ?tgt_bytes
          (unat tp) (build_index_spec ?src_bytes))))
        (of_nat (em_len (find_best_match_spec ?src_bytes ?tgt_bytes
          (unat tp) (build_index_spec ?src_bytes)))))"
    by (rule find_best_match'_early_eq_find_best_match_spec[
        OF True _ _ tp_le]) simp_all
  show ?thesis
    using result f_eq by simp
next
  case False
  show ?thesis
    by (rule find_best_match'_nonearly_eq_find_best_match_spec[
        OF rel closed nexts_wf tp_le tgt_ok False result])
qed

lemma find_best_match'_eq_find_best_match_spec_src_bytes:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len tp :: "32 word"
  assumes src_bytes_eq:
    "src_bytes = heap_bytes s src (unat src_len)"
      and rel:
    "source_index_heap_rel s src_bytes head_arr next_arr"
      and closed:
    "source_index_heap_chains_closed s src_bytes head_arr next_arr"
      and nexts_wf:
    "source_index_heap_nexts_wf s src_bytes next_arr"
      and tp_le: "tp \<le> tgt_len"
      and tgt_ok: "buf_valid s tgt (unat tgt_len)"
      and result:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m"
  shows "m = match_t_C
    (of_nat (em_pos (find_best_match_spec src_bytes
      (heap_bytes s tgt (unat tgt_len)) (unat tp)
      (build_index_spec src_bytes))))
    (of_nat (em_len (find_best_match_spec src_bytes
      (heap_bytes s tgt (unat tgt_len)) (unat tp)
      (build_index_spec src_bytes))))"
proof -
  have rel':
    "source_index_heap_rel s (heap_bytes s src (unat src_len)) head_arr next_arr"
    using rel src_bytes_eq by simp
  have closed':
    "source_index_heap_chains_closed s (heap_bytes s src (unat src_len))
      head_arr next_arr"
    using closed src_bytes_eq by simp
  have nexts_wf':
    "source_index_heap_nexts_wf s (heap_bytes s src (unat src_len)) next_arr"
    using nexts_wf src_bytes_eq by simp
  have exact:
    "m = match_t_C
      (of_nat (em_pos (find_best_match_spec
        (heap_bytes s src (unat src_len))
        (heap_bytes s tgt (unat tgt_len)) (unat tp)
        (build_index_spec (heap_bytes s src (unat src_len))))))
      (of_nat (em_len (find_best_match_spec
        (heap_bytes s src (unat src_len))
        (heap_bytes s tgt (unat tgt_len)) (unat tp)
        (build_index_spec (heap_bytes s src (unat src_len))))))"
    by (rule find_best_match'_eq_find_best_match_spec[
        OF rel' closed' nexts_wf' tp_le tgt_ok result])
  show ?thesis
    using exact src_bytes_eq by simp
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
  proof (cases "src_len < 4 \<or> tgt_len - tp < 4")
    case True
    hence m_eq: "m = match_t_C 0 0"
      using result find_best_match'_early_zero[of src_len tgt_len tp src tgt
          head_arr next_arr s]
      by simp
    show ?thesis
      using m_eq by simp
  next
    case False
    obtain h best_len best_pos cand checked :: "32 word" where ow_unfolded:
        "owhile
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
             cand :: 32 word, checked :: 32 word) s.
              cand \<noteq> no_entry32 \<and> checked < (0x10 :: 32 word))
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
             cand :: 32 word, checked :: 32 word) s.
              case if cand + 4 \<le> src_len
                   then case common_prefix' src cand src_len tgt tp tgt_len s of
                     None \<Rightarrow> None
                   | Some l \<Rightarrow>
                       Some (if 4 \<le> l \<and> best_len < l
                         then (l, cand) else (best_len, best_pos))
                   else Some (best_len, best_pos) of
                None \<Rightarrow> None
              | Some p \<Rightarrow>
                  (case p of
                   (best_len, best_pos) \<Rightarrow>
                     \<lambda>s. case if IS_VALID(32 word) s
                         (next_arr +\<^sub>p uint cand)
                       then Some () else None of
                         None \<Rightarrow> None
                       | Some _ \<Rightarrow>
                           Some (best_len, best_pos,
                             heap_w32 s (next_arr +\<^sub>p uint cand),
                             checked + (1 :: 32 word)))
                  s)
          ((0 :: 32 word), (0 :: 32 word),
            heap_w32 s (head_arr +\<^sub>p uint (h && 0xFFFF)),
            (0 :: 32 word)) s =
         Some (best_len, best_pos, cand, checked)"
      and m_eq: "m = match_t_C best_pos best_len"
      using result False
      unfolding find_best_match'_def
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: option.splits prod.splits if_splits)
    have ow:
      "owhile ?C ?B
        (0, 0, heap_w32 s (head_arr +\<^sub>p uint (h && 0xFFFF)), 0) s =
       Some (best_len, best_pos, cand, checked)"
      using ow_unfolded
      by (simp add: obind_def ocondition_def oreturn_def ogets_def
                    oguard_def K_def)
    have valid_best: "match_valid src_bytes tgt_bytes (unat tp)
        (unat best_pos) (unat best_len)"
      by (rule loop_valid_zero_some[OF ow])
    show ?thesis
      apply (subst m_eq)
      apply (subst match_t_C_sel_simps(1))
      apply (subst m_eq)
      apply (subst match_t_C_sel_simps(2))
      apply (rule valid_best)
      done
  qed
qed

lemma find_best_match'_match_valid_heap_bytes_if_common_prefix_cand_le:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len tp :: "32 word"
  assumes common_prefix_cand_le:
    "\<And>cand l. common_prefix' src cand src_len tgt tp tgt_len s = Some l \<Longrightarrow>
       cand \<le> src_len"
      and tp_le: "tp \<le> tgt_len"
      and result:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m"
  shows "match_valid
    (heap_bytes s src (unat src_len))
    (heap_bytes s tgt (unat tgt_len))
    (unat tp) (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
proof (rule find_best_match'_match_valid_if_common_prefix[OF _ result])
  fix cand l
  assume cp: "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
  show "match_valid
    (heap_bytes s src (unat src_len))
    (heap_bytes s tgt (unat tgt_len))
    (unat tp) (unat cand) (unat l)"
    by (rule common_prefix'_match_valid_heap_bytes[
          OF cp common_prefix_cand_le[OF cp] tp_le])
qed

lemma find_best_match'_match_valid_heap_bytes_source_index_nonearly:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len tp :: "32 word"
  assumes rel:
    "source_index_heap_rel s (heap_bytes s src (unat src_len)) head_arr next_arr"
      and nexts_wf:
    "source_index_heap_nexts_wf s (heap_bytes s src (unat src_len)) next_arr"
      and tp_le: "tp \<le> tgt_len"
      and not_early: "\<not> (src_len < 4 \<or> tgt_len - tp < 4)"
      and result:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m"
  shows "match_valid
    (heap_bytes s src (unat src_len))
    (heap_bytes s tgt (unat tgt_len))
    (unat tp) (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
proof -
  let ?src_bytes = "heap_bytes s src (unat src_len)"
  let ?tgt_bytes = "heap_bytes s tgt (unat tgt_len)"
  let ?cand_ok = "\<lambda>cand :: 32 word.
    cand = no_entry32 \<or> unat cand + min_match \<le> length ?src_bytes"
  let ?C = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word) s.
      cand \<noteq> no_entry32 \<and> checked < 0x10"
  let ?Update = "\<lambda>(best_len :: 32 word) (best_pos :: 32 word)
                    (cand :: 32 word).
      ocondition (\<lambda>s. cand + 4 \<le> src_len)
        (do {
          l <- common_prefix' src cand src_len tgt tp tgt_len;
          oreturn
            (if 4 \<le> l \<and> best_len < l then (l, cand)
             else (best_len, best_pos))
        })
        (oreturn (best_len, best_pos))"
  let ?After = "\<lambda>(cand :: 32 word) (checked :: 32 word)
                  (best_len :: 32 word, best_pos :: 32 word).
      do {
        oguard (\<lambda>s. IS_VALID(32 word) s (next_arr +\<^sub>p uint cand));
        ogets
          (\<lambda>s. (best_len, best_pos,
                heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1))
      }"
  let ?B = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                 cand :: 32 word, checked :: 32 word).
      do {
        p <- ?Update best_len best_pos cand;
        ?After cand checked p
      }"
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
  proof (goal_cases)
    case (1 hv)
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
    have head_ok_uint:
      "heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF)) = no_entry32 \<or>
       unat (heap_w32 s (head_arr +\<^sub>p uint (hv && 0xFFFF))) + min_match
          \<le> length ?src_bytes"
      using head_ok_int by (simp only: heap_eq)
    show ?case
      using head_ok_uint by simp
  qed
  have common_prefix_valid:
    "\<And>cand l. \<lbrakk>?cand_ok cand; cand \<noteq> no_entry32;
        common_prefix' src cand src_len tgt tp tgt_len s = Some l\<rbrakk>
      \<Longrightarrow> match_valid ?src_bytes ?tgt_bytes (unat tp) (unat cand) (unat l)"
  proof -
    fix cand l :: "32 word"
    assume cand_ok: "?cand_ok cand"
    assume cand_not_noentry: "cand \<noteq> no_entry32"
    assume cp: "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
    have cand_nat_le: "unat cand \<le> unat src_len"
      using cand_ok cand_not_noentry by simp
    have cand_le: "cand \<le> src_len"
      using cand_nat_le by (simp add: word_le_nat_alt)
    show "match_valid ?src_bytes ?tgt_bytes (unat tp) (unat cand) (unat l)"
      by (rule common_prefix'_match_valid_heap_bytes[OF cp cand_le tp_le])
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
    have next_ok_uint:
      "heap_w32 s (next_arr +\<^sub>p uint cand) = no_entry32 \<or>
       unat (heap_w32 s (next_arr +\<^sub>p uint cand)) + min_match
          \<le> length ?src_bytes"
      using next_ok_int by (simp only: heap_eq)
    show "?cand_ok (heap_w32 s (next_arr +\<^sub>p uint cand))"
      using next_ok_uint by simp
  qed
  have body_preserves:
    "\<And>best_len best_pos cand checked best_len' best_pos' cand' checked'.
      \<lbrakk>match_valid ?src_bytes ?tgt_bytes (unat tp)
          (unat best_pos) (unat best_len) \<and> ?cand_ok cand;
        cand \<noteq> no_entry32;
        ?B (best_len, best_pos, cand, checked) s =
          Some (best_len', best_pos', cand', checked')\<rbrakk>
      \<Longrightarrow> match_valid ?src_bytes ?tgt_bytes (unat tp)
            (unat best_pos') (unat best_len') \<and> ?cand_ok cand'"
  proof -
    fix best_len best_pos cand checked best_len' best_pos' cand' checked' :: "32 word"
    assume inv:
      "match_valid ?src_bytes ?tgt_bytes (unat tp)
        (unat best_pos) (unat best_len) \<and> ?cand_ok cand"
    assume cand_not_noentry: "cand \<noteq> no_entry32"
    assume body:
      "?B (best_len, best_pos, cand, checked) s =
        Some (best_len', best_pos', cand', checked')"
    have body_obind:
      "obind (?Update best_len best_pos cand) (?After cand checked) s =
        Some (best_len', best_pos', cand', checked')"
      using body by simp
    obtain upd where upd_res0: "?Update best_len best_pos cand s = Some upd"
      and after_res: "?After cand checked upd s =
        Some (best_len', best_pos', cand', checked')"
      using reader_obind_SomeE[OF body_obind] by blast
    obtain upd_len upd_pos where upd_eq: "upd = (upd_len, upd_pos)"
      by (cases upd) auto
    let ?valid_next = "IS_VALID(32 word) s (next_arr +\<^sub>p uint cand)"
    have after_res_pair:
      "?After cand checked (upd_len, upd_pos) s =
        Some (best_len', best_pos', cand', checked')"
      using after_res upd_eq by simp
    have after_unfold:
      "?After cand checked (upd_len, upd_pos) s =
        (if ?valid_next
         then Some (upd_len, upd_pos,
           heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1)
         else None)"
      by (simp add: obind_def oguard_def ogets_def K_def)
    have after_tuple_eq:
      "(upd_len, upd_pos, heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1) =
       (best_len', best_pos', cand', checked')"
      using after_res_pair after_unfold
      by (cases ?valid_next) simp_all
    have best_len'_eq: "best_len' = upd_len"
      and best_pos'_eq: "best_pos' = upd_pos"
      and cand'_eq: "cand' = heap_w32 s (next_arr +\<^sub>p uint cand)"
      and checked'_eq: "checked' = checked + 1"
      using after_tuple_eq by simp_all
    have upd_valid:
      "match_valid ?src_bytes ?tgt_bytes (unat tp)
        (unat upd_pos) (unat upd_len)"
    proof (cases "cand + 4 \<le> src_len")
      case False
      have "?Update best_len best_pos cand s = Some (best_len, best_pos)"
        using False by (simp add: ocondition_def oreturn_def K_def)
      hence "(upd_len, upd_pos) = (best_len, best_pos)"
        using upd_res0 upd_eq by simp
      thus ?thesis
        using inv by simp
    next
      case True
      have upd_do:
        "(do {
           l <- common_prefix' src cand src_len tgt tp tgt_len;
           oreturn
             (if 4 \<le> l \<and> best_len < l then (l, cand)
              else (best_len, best_pos))
         }) s = Some (upd_len, upd_pos)"
        using upd_res0 upd_eq True
        by (simp add: ocondition_def)
      obtain l where cp:
        "common_prefix' src cand src_len tgt tp tgt_len s = Some l"
        and upd_pair:
        "(upd_len, upd_pos) =
          (if 4 \<le> l \<and> best_len < l then (l, cand)
           else (best_len, best_pos))"
      proof (cases "common_prefix' src cand src_len tgt tp tgt_len s")
        case None
        thus ?thesis
          using upd_do by (simp add: obind_def)
      next
        case (Some l)
        have "(upd_len, upd_pos) =
          (if 4 \<le> l \<and> best_len < l then (l, cand)
           else (best_len, best_pos))"
          using upd_do Some by (simp add: obind_def oreturn_def K_def)
        thus ?thesis
          using Some that by blast
      qed
      show ?thesis
      proof (cases "4 \<le> l \<and> best_len < l")
        case True
        have "match_valid ?src_bytes ?tgt_bytes (unat tp) (unat cand) (unat l)"
          by (rule common_prefix_valid[OF _ cand_not_noentry cp]) (use inv in simp)
        thus ?thesis
          using upd_pair True by simp
      next
        case False
        have upd_old: "(upd_len, upd_pos) = (best_len, best_pos)"
          using upd_pair False by simp
        show ?thesis
          using upd_old inv by simp
      qed
    qed
    have preserved_match:
      "match_valid ?src_bytes ?tgt_bytes (unat tp)
        (unat best_pos') (unat best_len')"
      using upd_valid best_len'_eq best_pos'_eq by simp
    have preserved_cand: "?cand_ok cand'"
      using inv cand_not_noentry cand'_eq next_cand_ok[of cand] by simp
    show "match_valid ?src_bytes ?tgt_bytes (unat tp)
            (unat best_pos') (unat best_len') \<and> ?cand_ok cand'"
      using preserved_match preserved_cand by simp
  qed
  have body_decreases:
    "\<And>best_len best_pos cand checked best_len' best_pos' cand' checked'.
      \<lbrakk>checked < 0x10;
        ?B (best_len, best_pos, cand, checked) s =
          Some (best_len', best_pos', cand', checked')\<rbrakk>
      \<Longrightarrow> 16 - unat checked' < 16 - unat checked"
  proof -
    fix best_len best_pos cand checked best_len' best_pos' cand' checked' :: "32 word"
    assume checked_lt: "checked < 0x10"
    assume body:
      "?B (best_len, best_pos, cand, checked) s =
        Some (best_len', best_pos', cand', checked')"
    have body_obind:
      "obind (?Update best_len best_pos cand) (?After cand checked) s =
        Some (best_len', best_pos', cand', checked')"
      using body by simp
    obtain upd where after_res:
      "?After cand checked upd s = Some (best_len', best_pos', cand', checked')"
      using reader_obind_SomeE[OF body_obind] by blast
    obtain upd_len upd_pos where upd_eq: "upd = (upd_len, upd_pos)"
      by (cases upd) auto
    let ?valid_next = "IS_VALID(32 word) s (next_arr +\<^sub>p uint cand)"
    have after_res_pair:
      "?After cand checked (upd_len, upd_pos) s =
        Some (best_len', best_pos', cand', checked')"
      using after_res upd_eq by simp
    have after_unfold:
      "?After cand checked (upd_len, upd_pos) s =
        (if ?valid_next
         then Some (upd_len, upd_pos,
           heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1)
         else None)"
      by (simp add: obind_def oguard_def ogets_def K_def)
    have after_tuple_eq:
      "(upd_len, upd_pos, heap_w32 s (next_arr +\<^sub>p uint cand), checked + 1) =
       (best_len', best_pos', cand', checked')"
      using after_res_pair after_unfold
      by (cases ?valid_next) simp_all
    have checked'_eq: "checked' = checked + 1"
      using after_tuple_eq by simp
    show "16 - unat checked' < 16 - unat checked"
      using checked_measure_decreases[OF checked_lt] checked'_eq by simp
  qed
  have loop_preserves:
    "\<And>init. (case init of (best_len, best_pos, cand, checked) \<Rightarrow>
        match_valid ?src_bytes ?tgt_bytes (unat tp)
          (unat best_pos) (unat best_len) \<and> ?cand_ok cand) \<Longrightarrow>
      case owhile ?C ?B init s of
        None \<Rightarrow> True
      | Some (best_len, best_pos, cand, checked) \<Rightarrow>
          match_valid ?src_bytes ?tgt_bytes (unat tp)
            (unat best_pos) (unat best_len)"
    apply (rule Reader_Monad.owhile_rule[
      where I = "\<lambda>(best_len :: 32 word, best_pos :: 32 word,
                     cand :: 32 word, checked :: 32 word) s.
          match_valid ?src_bytes ?tgt_bytes (unat tp)
            (unat best_pos) (unat best_len) \<and> ?cand_ok cand"
        and M = "measure
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
               cand :: 32 word, checked :: 32 word). 16 - unat checked)"])
       apply (simp split: prod.splits)
      apply simp
    subgoal for r r'
      apply (cases r; cases r')
      apply (clarsimp simp: ogets_def K_def intro!: checked_measure_decreases)
      done
    subgoal premises prems for r r' r''
    proof -
      obtain best_len best_pos cand checked where cur_eq:
        "r' = (best_len, best_pos, cand, checked)"
        by (cases r') auto
      obtain best_len' best_pos' cand' checked' where res_eq:
        "r'' = (best_len', best_pos', cand', checked')"
        by (cases r'') auto
      have inv:
        "match_valid ?src_bytes ?tgt_bytes (unat tp)
          (unat best_pos) (unat best_len) \<and> ?cand_ok cand"
        using prems(2) cur_eq by simp
      have cand_not_noentry: "cand \<noteq> no_entry32"
        using prems(3) cur_eq by simp
      have body:
        "?B (best_len, best_pos, cand, checked) s =
          Some (best_len', best_pos', cand', checked')"
        using prems(4) cur_eq res_eq by simp
      have preserved:
        "match_valid ?src_bytes ?tgt_bytes (unat tp)
          (unat best_pos') (unat best_len') \<and> ?cand_ok cand'"
        by (rule body_preserves[OF inv cand_not_noentry body])
      show ?thesis
        using preserved res_eq by simp
    qed
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
        match_valid ?src_bytes ?tgt_bytes (unat tp)
          (unat init_pos) (unat init_len) \<and> ?cand_ok init_cand) \<Longrightarrow>
      match_valid ?src_bytes ?tgt_bytes (unat tp)
        (unat best_pos) (unat best_len)"
  proof -
    fix init :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word"
    fix best_len best_pos cand checked :: "32 word"
    assume ow:
      "owhile ?C ?B init s = Some (best_len, best_pos, cand, checked)"
    assume init_inv:
      "case init of (init_len, init_pos, init_cand, init_checked) \<Rightarrow>
        match_valid ?src_bytes ?tgt_bytes (unat tp)
          (unat init_pos) (unat init_len) \<and> ?cand_ok init_cand"
    have "case owhile ?C ?B init s of
        None \<Rightarrow> True
      | Some (best_len, best_pos, cand, checked) \<Rightarrow>
          match_valid ?src_bytes ?tgt_bytes (unat tp)
            (unat best_pos) (unat best_len)"
      using loop_preserves[OF init_inv] .
    thus "match_valid ?src_bytes ?tgt_bytes (unat tp)
        (unat best_pos) (unat best_len)"
      using ow by simp
  qed
  have loop_valid_zero_some:
    "\<And>(cand0 :: 32 word) (best_len :: 32 word) (best_pos :: 32 word)
        (cand :: 32 word) (checked :: 32 word).
      ?cand_ok cand0 \<Longrightarrow>
      owhile ?C ?B
        ((0 :: 32 word), ((0 :: 32 word), (cand0, (0 :: 32 word)))) s =
        Some (best_len, best_pos, cand, checked) \<Longrightarrow>
      match_valid ?src_bytes ?tgt_bytes (unat tp)
        (unat best_pos) (unat best_len)"
    apply (rule loop_valid_some)
     apply assumption
    apply simp
    done
  show ?thesis
  proof -
    obtain h best_len best_pos cand checked :: "32 word" where ow_unfolded:
        "owhile
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
             cand :: 32 word, checked :: 32 word) s.
              cand \<noteq> no_entry32 \<and> checked < (0x10 :: 32 word))
          (\<lambda>(best_len :: 32 word, best_pos :: 32 word,
             cand :: 32 word, checked :: 32 word) s.
              case if cand + 4 \<le> src_len
                   then case common_prefix' src cand src_len tgt tp tgt_len s of
                     None \<Rightarrow> None
                   | Some l \<Rightarrow>
                       Some (if 4 \<le> l \<and> best_len < l
                         then (l, cand) else (best_len, best_pos))
                   else Some (best_len, best_pos) of
                None \<Rightarrow> None
              | Some p \<Rightarrow>
                  (case p of
                   (best_len, best_pos) \<Rightarrow>
                     \<lambda>s. case if IS_VALID(32 word) s
                         (next_arr +\<^sub>p uint cand)
                       then Some () else None of
                         None \<Rightarrow> None
                       | Some _ \<Rightarrow>
                           Some (best_len, best_pos,
                             heap_w32 s (next_arr +\<^sub>p uint cand),
                             checked + (1 :: 32 word)))
                  s)
          ((0 :: 32 word), (0 :: 32 word),
            heap_w32 s (head_arr +\<^sub>p uint (h && 0xFFFF)),
            (0 :: 32 word)) s =
         Some (best_len, best_pos, cand, checked)"
      and m_eq: "m = match_t_C best_pos best_len"
      using result not_early
      unfolding find_best_match'_def
      by (auto simp: obind_def ocondition_def oreturn_def ogets_def
                     oguard_def K_def
               split: option.splits prod.splits if_splits)
    have cand0_ok:
      "?cand_ok (heap_w32 s (head_arr +\<^sub>p uint (h && 0xFFFF)))"
      using initial_cand_ok[of h] by simp
    have ow:
      "owhile ?C ?B
        (0, 0, heap_w32 s (head_arr +\<^sub>p uint (h && 0xFFFF)), 0) s =
       Some (best_len, best_pos, cand, checked)"
      using ow_unfolded
      by (simp add: obind_def ocondition_def oreturn_def ogets_def
                    oguard_def K_def)
    have valid_best:
      "match_valid ?src_bytes ?tgt_bytes (unat tp)
        (unat best_pos) (unat best_len)"
      by (rule loop_valid_zero_some[OF cand0_ok ow])
    show ?thesis
      apply (subst m_eq)
      apply (subst match_t_C_sel_simps(1))
      apply (subst m_eq)
      apply (subst match_t_C_sel_simps(2))
      apply (rule valid_best)
      done
  qed
qed

lemma find_best_match'_match_valid_heap_bytes_source_index:
  fixes src tgt :: "8 word ptr"
    and src_len tgt_len tp :: "32 word"
  assumes rel:
    "source_index_heap_rel s (heap_bytes s src (unat src_len)) head_arr next_arr"
      and nexts_wf:
    "source_index_heap_nexts_wf s (heap_bytes s src (unat src_len)) next_arr"
      and tp_le: "tp \<le> tgt_len"
      and result:
    "find_best_match' src src_len tgt tgt_len tp head_arr next_arr s = Some m"
  shows "match_valid
    (heap_bytes s src (unat src_len))
    (heap_bytes s tgt (unat tgt_len))
    (unat tp) (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
proof (cases "src_len < 4 \<or> tgt_len - tp < 4")
  case True
  hence m_eq: "m = match_t_C 0 0"
    using result find_best_match'_early_zero[of src_len tgt_len tp src tgt
        head_arr next_arr s]
    by simp
  show ?thesis
    by (simp add: m_eq)
next
  case False
  show ?thesis
    by (rule find_best_match'_match_valid_heap_bytes_source_index_nonearly[
          OF rel nexts_wf tp_le False result])
qed

end

end
