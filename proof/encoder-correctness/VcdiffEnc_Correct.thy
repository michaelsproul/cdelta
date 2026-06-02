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
