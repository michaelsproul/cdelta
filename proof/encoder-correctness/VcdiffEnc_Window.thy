theory VcdiffEnc_Window
  imports
    VcdiffEnc_Emit
    VcdiffEnc_Match
begin


(*
  Pure shape of the main encode_window loop invariant. The C-level invariant
  will add heap, cursor, cache, and capacity facts around this prefix split.
*)
definition encoder_loop_inv :: "byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> bool" where
  "encoder_loop_inv tgt tp flushed pending \<longleftrightarrow>
     tp \<le> length tgt \<and> flushed @ pending = take tp tgt"

lemma encoder_loop_invI:
  assumes "tp \<le> length tgt"
      and "flushed @ pending = take tp tgt"
  shows "encoder_loop_inv tgt tp flushed pending"
  using assms by (simp add: encoder_loop_inv_def)

lemma encoder_loop_invD:
  assumes "encoder_loop_inv tgt tp flushed pending"
  shows "tp \<le> length tgt" "flushed @ pending = take tp tgt"
  using assms by (simp_all add: encoder_loop_inv_def)

lemma encoder_loop_inv_tp_le:
  assumes "encoder_loop_inv tgt tp flushed pending"
  shows "tp \<le> length tgt"
  using assms by (simp add: encoder_loop_inv_def)

lemma encoder_loop_inv_prefix_eq:
  assumes "encoder_loop_inv tgt tp flushed pending"
  shows "flushed @ pending = take tp tgt"
  using assms by (simp add: encoder_loop_inv_def)

lemma encoder_loop_inv_lengths:
  assumes "encoder_loop_inv tgt tp flushed pending"
  shows "length flushed + length pending = tp"
proof -
  have tp_le: "tp \<le> length tgt"
    and prefix: "flushed @ pending = take tp tgt"
    using encoder_loop_invD[OF assms] by simp_all
  have "length flushed + length pending = length (flushed @ pending)"
    by simp
  also have "... = length (take tp tgt)"
    using prefix by simp
  also have "... = tp"
    using tp_le by simp
  finally show ?thesis .
qed

lemma encoder_loop_inv_flushed_length_le:
  assumes "encoder_loop_inv tgt tp flushed pending"
  shows "length flushed \<le> tp"
  using encoder_loop_inv_lengths[OF assms] by simp

lemma encoder_loop_inv_pending_length_le:
  assumes "encoder_loop_inv tgt tp flushed pending"
  shows "length pending \<le> tp"
  using encoder_loop_inv_lengths[OF assms] by simp

lemma encoder_loop_inv_flushed_eq_take:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
  shows "flushed = take (length flushed) tgt"
proof -
  have "flushed = take (length flushed) (flushed @ pending)"
    by simp
  also have "... = take (length flushed) (take tp tgt)"
    using encoder_loop_inv_prefix_eq[OF inv] by simp
  also have "... = take (length flushed) tgt"
    using encoder_loop_inv_flushed_length_le[OF inv] by simp
  finally show ?thesis .
qed

lemma drop_take_add_eq_take_drop:
  "drop m (take (m + n) xs) = take n (drop m xs)"
proof (induction m arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case by (cases xs) simp_all
qed

lemma encoder_loop_inv_pending_eq_drop_take:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
  shows "pending = drop (length flushed) (take tp tgt)"
proof -
  have "pending = drop (length flushed) (flushed @ pending)"
    by simp
  also have "... = drop (length flushed) (take tp tgt)"
    using encoder_loop_inv_prefix_eq[OF inv] by simp
  finally show ?thesis .
qed

lemma encoder_loop_inv_pending_eq_take_drop:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
  shows "pending = take (length pending) (drop (length flushed) tgt)"
proof -
  have len: "length flushed + length pending = tp"
    by (rule encoder_loop_inv_lengths[OF inv])
  have "pending = drop (length flushed) (take tp tgt)"
    by (rule encoder_loop_inv_pending_eq_drop_take[OF inv])
  also have "... = drop (length flushed)
      (take (length flushed + length pending) tgt)"
    using len by simp
  also have "... = take (length pending) (drop (length flushed) tgt)"
    by (rule drop_take_add_eq_take_drop)
  finally show ?thesis .
qed

lemma encoder_loop_inv_target_prefix:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
  shows "take (length flushed) tgt @ pending = take tp tgt"
  using encoder_loop_inv_flushed_eq_take[OF inv]
        encoder_loop_inv_prefix_eq[OF inv]
  by simp

lemma encoder_loop_inv_empty[simp]:
  "encoder_loop_inv tgt 0 [] []"
  by (simp add: encoder_loop_inv_def)

lemma encoder_loop_inv_flush_pending:
  assumes "encoder_loop_inv tgt tp flushed pending"
  shows "encoder_loop_inv tgt tp (flushed @ pending) []"
  using assms by (simp add: encoder_loop_inv_def)

lemma encoder_loop_inv_pending_step:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
      and tp_lt: "tp < length tgt"
  shows "encoder_loop_inv tgt (Suc tp) flushed (pending @ [tgt ! tp])"
proof -
  have "flushed @ (pending @ [tgt ! tp]) = take (Suc tp) tgt"
    using encoder_loop_inv_prefix_eq[OF inv] tp_lt
    by (simp add: take_Suc_conv_app_nth)
  then show ?thesis
    using tp_lt by (simp add: encoder_loop_inv_def)
qed

lemma encoder_loop_inv_pending_step_word:
  fixes tp tgt_len :: "32 word"
  assumes inv: "encoder_loop_inv tgt (unat tp) flushed pending"
      and tp_lt: "tp < tgt_len"
      and tgt_len: "length tgt = unat tgt_len"
  shows "encoder_loop_inv tgt (unat (tp + 1)) flushed
           (pending @ [tgt ! unat tp])"
proof -
  have tp_nat_lt: "unat tp < length tgt"
    using tp_lt tgt_len by (simp add: word_less_nat_alt)
  have tp_suc: "unat (tp + 1) = Suc (unat tp)"
    using tp_lt by unat_arith
  show ?thesis
    using encoder_loop_inv_pending_step[OF inv tp_nat_lt]
    by (simp add: tp_suc)
qed

lemma encoder_loop_inv_advance:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
      and adv: "tp + n \<le> length tgt"
      and chunk: "chunk = take n (drop tp tgt)"
  shows "encoder_loop_inv tgt (tp + n) (flushed @ pending @ chunk) []"
proof -
  have "take (tp + n) tgt = take tp tgt @ take n (drop tp tgt)"
    by (simp add: take_add)
  then have "(flushed @ pending @ chunk) @ [] = take (tp + n) tgt"
    using encoder_loop_inv_prefix_eq[OF inv] chunk by simp
  then show ?thesis
    using adv by (simp add: encoder_loop_inv_def)
qed

lemma encoder_loop_inv_advance_empty_pending:
  assumes inv: "encoder_loop_inv tgt tp flushed []"
      and adv: "tp + n \<le> length tgt"
  shows "encoder_loop_inv tgt (tp + n)
           (flushed @ take n (drop tp tgt)) []"
  using encoder_loop_inv_advance[OF inv adv, of "take n (drop tp tgt)"]
  by simp

lemma encoder_loop_inv_doneD:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
      and tp_done: "tp = length tgt"
  shows "flushed @ pending = tgt"
  using encoder_loop_inv_prefix_eq[OF inv] tp_done by simp

lemma encoder_loop_inv_done_no_pendingD:
  assumes inv: "encoder_loop_inv tgt tp flushed []"
      and tp_done: "tp = length tgt"
  shows "flushed = tgt"
  using encoder_loop_inv_doneD[OF inv tp_done] by simp

lemma match_validD:
  assumes mv: "match_valid src tgt tp pos len"
      and len_pos: "0 < len"
  shows "pos + len \<le> length src"
        "tp + len \<le> length tgt"
        "take len (drop pos src) = take len (drop tp tgt)"
  using mv len_pos by (simp_all add: match_valid_def)

lemma match_valid_take:
  assumes mv: "match_valid src tgt tp pos len"
      and n_le: "n \<le> len"
  shows "match_valid src tgt tp pos n"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have n_pos: "0 < n"
    by simp
  then have len_pos: "0 < len"
    using n_le by simp
  have src_bound: "pos + len \<le> length src"
    and tgt_bound: "tp + len \<le> length tgt"
    and eq: "take len (drop pos src) = take len (drop tp tgt)"
    using match_validD[OF mv len_pos] by simp_all
  have "take n (drop pos src) = take n (take len (drop pos src))"
    using n_le by simp
  also have "... = take n (take len (drop tp tgt))"
    using eq by simp
  also have "... = take n (drop tp tgt)"
    using n_le by simp
  finally have take_eq:
    "take n (drop pos src) = take n (drop tp tgt)" .
  show ?thesis
    using src_bound tgt_bound n_le n_pos take_eq
    by (auto simp: match_valid_def)
qed

lemma match_valid_drop:
  assumes mv: "match_valid src tgt tp pos len"
      and n_le: "n \<le> len"
  shows "match_valid src tgt (tp + n) (pos + n) (len - n)"
proof (cases "len = n")
  case True
  then show ?thesis by simp
next
  case False
  then have rest_pos: "0 < len - n"
    using n_le by simp
  have len_pos: "0 < len"
    using rest_pos n_le by simp
  have src_bound: "pos + len \<le> length src"
    and tgt_bound: "tp + len \<le> length tgt"
    and eq: "take len (drop pos src) = take len (drop tp tgt)"
    using match_validD[OF mv len_pos] by simp_all
  have src_drop:
    "take (len - n) (drop (pos + n) src) =
     drop n (take len (drop pos src))"
    using n_le by (simp add: drop_take drop_drop add.commute)
  have tgt_drop:
    "take (len - n) (drop (tp + n) tgt) =
     drop n (take len (drop tp tgt))"
    using n_le by (simp add: drop_take drop_drop add.commute)
  have take_eq:
    "take (len - n) (drop (pos + n) src) =
     take (len - n) (drop (tp + n) tgt)"
    using src_drop tgt_drop eq by simp
  show ?thesis
    using src_bound tgt_bound n_le rest_pos take_eq
    by (auto simp: match_valid_def)
qed

lemma encoder_loop_inv_advance_match:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
      and mv: "match_valid src tgt tp pos len"
      and len_pos: "0 < len"
  shows "encoder_loop_inv tgt (tp + len)
           (flushed @ pending @ take len (drop pos src)) []"
proof -
  have tgt_bound: "tp + len \<le> length tgt"
    and take_eq: "take len (drop pos src) = take len (drop tp tgt)"
    using match_validD[OF mv len_pos] by simp_all
  show ?thesis
    using encoder_loop_inv_advance[OF inv tgt_bound, of "take len (drop pos src)"]
          take_eq
    by simp
qed

lemma encoder_loop_inv_advance_match_prefix:
  assumes inv: "encoder_loop_inv tgt tp flushed pending"
      and mv: "match_valid src tgt tp pos len"
      and n_pos: "0 < n"
      and n_le: "n \<le> len"
  shows "encoder_loop_inv tgt (tp + n)
           (flushed @ pending @ take n (drop pos src)) []"
  using encoder_loop_inv_advance_match[OF inv match_valid_take[OF mv n_le] n_pos] .

lemma encoder_loop_inv_advance_match_word:
  fixes tp len :: "32 word"
  assumes inv: "encoder_loop_inv tgt (unat tp) flushed pending"
      and mv: "match_valid src tgt (unat tp) pos (unat len)"
      and len_pos: "0 < unat len"
      and no_overflow: "unat tp + unat len < 2 ^ 32"
  shows "encoder_loop_inv tgt (unat (tp + len))
           (flushed @ pending @ take (unat len) (drop pos src)) []"
proof -
  have tp_len: "unat (tp + len) = unat tp + unat len"
    using no_overflow by (simp add: unat_word_ariths(1))
  show ?thesis
    using encoder_loop_inv_advance_match[OF inv mv len_pos]
    by (simp add: tp_len)
qed

lemma section_decodes_empty[simp]:
  "section_decodes src_seg tgt_len [] [] [] [] cache_init"
  by (simp add: section_decodes_def section_decodes_prefix_def)

context vcdiff_enc_global_addresses begin

lemma enc_sections_inv_empty:
  assumes "sections_t_C.data_pos_C sec = 0"
      and "sections_t_C.inst_pos_C sec = 0"
      and "sections_t_C.addr_pos_C sec = 0"
  shows "enc_sections_inv st data inst addr sec src_seg tgt_len
           [] [] [] [] cache_init"
  using assms
  by (simp add: enc_sections_inv_def emitted_sections_def heap_bytes_def)

definition encode_window_c_loop_inv ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   sections_t_C \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> cache \<Rightarrow> bool" where
  "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out \<longleftrightarrow>
     sections_t_C.err_C sec = ENC_OK \<and>
     length src_seg = unat src_len \<and>
     length tgt_bytes = unat tgt_len \<and>
     heap_bytes st src (length src_seg) = src_seg \<and>
     heap_bytes st tgt (length tgt_bytes) = tgt_bytes \<and>
     heap_bytes st pending (unat pend_len) = pending_bytes \<and>
     length pending_bytes = unat pend_len \<and>
     unat pend_len \<le> unat pending_cap \<and>
     unat (sections_t_C.data_pos_C sec) \<le> unat data_cap \<and>
     unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap \<and>
     unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap \<and>
     encoder_loop_inv tgt_bytes (unat tp) flushed pending_bytes \<and>
     enc_sections_inv st data inst addr sec src_seg (length tgt_bytes)
       data_bytes inst_bytes addr_bytes flushed c_out"

lemma encode_window_c_loop_invD:
  assumes inv: "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
  shows "sections_t_C.err_C sec = ENC_OK"
        "length src_seg = unat src_len"
        "length tgt_bytes = unat tgt_len"
        "heap_bytes st src (length src_seg) = src_seg"
        "heap_bytes st tgt (length tgt_bytes) = tgt_bytes"
        "heap_bytes st pending (unat pend_len) = pending_bytes"
        "length pending_bytes = unat pend_len"
        "unat pend_len \<le> unat pending_cap"
        "unat (sections_t_C.data_pos_C sec) \<le> unat data_cap"
        "unat (sections_t_C.inst_pos_C sec) \<le> unat inst_cap"
        "unat (sections_t_C.addr_pos_C sec) \<le> unat addr_cap"
        "encoder_loop_inv tgt_bytes (unat tp) flushed pending_bytes"
        "enc_sections_inv st data inst addr sec src_seg (length tgt_bytes)
           data_bytes inst_bytes addr_bytes flushed c_out"
  using inv by (auto simp: encode_window_c_loop_inv_def)

lemma encode_window_c_loop_inv_tp_le_tgt_len:
  assumes inv: "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
  shows "unat tp \<le> unat tgt_len"
  using encode_window_c_loop_invD(3,12)[OF inv]
        encoder_loop_inv_tp_le[of tgt_bytes "unat tp" flushed pending_bytes]
  by simp

lemma encode_window_c_loop_inv_prefix_eq:
  assumes inv: "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
  shows "flushed @ pending_bytes = take (unat tp) tgt_bytes"
  using encode_window_c_loop_invD(12)[OF inv]
  by (rule encoder_loop_inv_prefix_eq)

definition encode_window_c_loop_cache_inv ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   sections_t_C \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> cache \<Rightarrow> bool" where
  "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out \<longleftrightarrow>
     encode_window_c_loop_inv st
       src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
       pending pending_cap sec tp pend_len
       src_seg tgt_bytes data_bytes inst_bytes addr_bytes
       flushed pending_bytes c_out \<and>
     enc_cache_abs st c_out \<and>
     enc_cache_wf c_out"

lemma encode_window_c_loop_cache_invD:
  assumes inv: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
  shows "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
    and "enc_cache_abs st c_out"
    and "enc_cache_wf c_out"
  using inv by (simp_all add: encode_window_c_loop_cache_inv_def)

definition encode_window_match_ok ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow> bool" where
  "encode_window_match_ok st src src_len tgt tgt_len head_p next_p
     src_seg tgt_bytes \<longleftrightarrow>
     (\<forall>tp. tp < tgt_len \<longrightarrow>
       (\<exists>m.
          find_best_match' src src_len tgt tgt_len tp head_p next_p st =
            Some m \<and>
          match_valid src_seg tgt_bytes (unat tp)
            (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))))"

lemma encode_window_match_okD:
  assumes ok: "encode_window_match_ok st src src_len tgt tgt_len
     head_p next_p src_seg tgt_bytes"
      and tp_lt: "tp < tgt_len"
  obtains m where
    "find_best_match' src src_len tgt tgt_len tp head_p next_p st = Some m"
    "match_valid src_seg tgt_bytes (unat tp)
       (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
  using ok tp_lt by (auto simp: encode_window_match_ok_def)

definition encode_window_buffers_ok ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow> bool" where
  "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap \<longleftrightarrow>
     buf_valid st src (unat src_len) \<and>
     buf_valid st tgt (unat tgt_len) \<and>
     buf_valid st data (unat data_cap) \<and>
     buf_valid st inst (unat inst_cap) \<and>
     buf_valid st addr (unat addr_cap) \<and>
     buf_valid st pending (unat pending_cap) \<and>
     ptr_range_distinct data (unat data_cap) \<and>
     ptr_range_distinct inst (unat inst_cap) \<and>
     ptr_range_distinct addr (unat addr_cap) \<and>
     ptr_range_distinct pending (unat pending_cap) \<and>
     bufs_disjoint src (unat src_len) pending (unat pending_cap) \<and>
     bufs_disjoint tgt (unat tgt_len) pending (unat pending_cap) \<and>
     bufs_disjoint data (unat data_cap) pending (unat pending_cap) \<and>
     bufs_disjoint inst (unat inst_cap) pending (unat pending_cap) \<and>
     bufs_disjoint addr (unat addr_cap) pending (unat pending_cap) \<and>
     bufs_disjoint data (unat data_cap) inst (unat inst_cap) \<and>
     bufs_disjoint data (unat data_cap) addr (unat addr_cap) \<and>
     bufs_disjoint inst (unat inst_cap) addr (unat addr_cap)"

lemma encode_window_buffers_ok_heap_w8_update[simp]:
  "encode_window_buffers_ok (heap_w8_update f st)
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap =
   encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
  by (simp add: encode_window_buffers_ok_def)

lemma encode_window_buffers_ok_heap_typing_eq:
  assumes "heap_typing t = heap_typing s"
      and "encode_window_buffers_ok s
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
  shows "encode_window_buffers_ok t
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
  using assms by (simp add: encode_window_buffers_ok_def buf_valid_def)

definition encode_window_c_loop_body ::
  "8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word \<times> sections_t_C \<times> 32 word \<Rightarrow>
   (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
    lifted_globals) exn_monad" where
  "encode_window_c_loop_body
     src src_len tgt tgt_len head_p next_p
     data data_cap inst inst_cap addr addr_cap pending pending_cap =
   (\<lambda>(pend_len, sec, tp). do {
      m \<leftarrow> gets_the
            (find_best_match' src src_len tgt tgt_len tp head_p next_p);
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
           here \<leftarrow> return (src_len + tp);
           f \<leftarrow> liftE
                (try_emit_add_copy' sec data data_cap inst inst_cap
                  addr addr_cap pending pend_len
                  (match_t_C.pos_C m) here (match_t_C.len_C m));
           unless (sections_t_C.err_C (fused_t_C.s_C f) = 0)
            (throw (fused_t_C.s_C f));
           condition (\<lambda>s. fused_t_C.fused_C f \<noteq> 0)
             (do {
                consumed \<leftarrow> return (fused_t_C.fused_C f);
                sec \<leftarrow> return (fused_t_C.s_C f);
                tp \<leftarrow> return (tp + consumed);
                (sec, tp) \<leftarrow>
                  condition (\<lambda>s. consumed < match_t_C.len_C m)
                    (do {
                       rem \<leftarrow> return (match_t_C.len_C m - consumed);
                       sec \<leftarrow> liftE
                         (emit_copy' sec inst inst_cap addr addr_cap
                           (match_t_C.pos_C m + consumed)
                           (src_len + tp) rem);
                       unless (sections_t_C.err_C sec = 0) (throw sec);
                       return (sec, tp + rem)
                     })
                    (return (sec, tp));
                return (0, sec, tp)
              })
             (do {
                (pend_len, sec, tp) \<leftarrow> return (pend_len, sec, tp);
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
                    (match_t_C.pos_C m) here (match_t_C.len_C m));
                unless (sections_t_C.err_C sec = 0) (throw sec);
                return (pend_len, sec, tp + match_t_C.len_C m)
              })
         })
    })"

lemma encode_window_buffers_ok_pending_dist:
  assumes ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and pend_lt: "pend_len < pending_cap"
  shows "ptr_range_distinct pending (Suc (unat pend_len))"
proof -
  have dist: "ptr_range_distinct pending (unat pending_cap)"
    using ok by (simp add: encode_window_buffers_ok_def)
  have suc_le: "unat (pend_len + 1) \<le> unat pending_cap"
    using pend_lt by (rule unat_suc_le_of_word_less)
  have "Suc (unat pend_len) \<le> unat pending_cap"
    using suc_le unat_word_suc_of_less[OF pend_lt] by simp
  thus ?thesis
    by (rule ptr_range_distinct_mono[OF dist])
qed

lemma encode_window_buffers_ok_src_pending_disj:
  assumes ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and i_lt: "i < unat src_len"
      and pend_lt: "pend_len < pending_cap"
  shows "src +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
proof -
  have disj: "bufs_disjoint src (unat src_len) pending (unat pending_cap)"
    using ok by (simp add: encode_window_buffers_ok_def)
  have p_lt: "unat pend_len < unat pending_cap"
    using pend_lt by (simp add: word_less_nat_alt)
  have ne: "src +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
    using disj i_lt p_lt
    unfolding bufs_disjoint_def by blast
  thus ?thesis
    by (subst uint_nat)
qed

lemma encode_window_buffers_ok_tgt_pending_disj:
  assumes ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and i_lt: "i < unat tgt_len"
      and pend_lt: "pend_len < pending_cap"
  shows "tgt +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
proof -
  have disj: "bufs_disjoint tgt (unat tgt_len) pending (unat pending_cap)"
    using ok by (simp add: encode_window_buffers_ok_def)
  have p_lt: "unat pend_len < unat pending_cap"
    using pend_lt by (simp add: word_less_nat_alt)
  have ne: "tgt +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
    using disj i_lt p_lt
    unfolding bufs_disjoint_def by blast
  thus ?thesis
    by (subst uint_nat)
qed

lemma encode_window_buffers_ok_data_pending_disj:
  assumes ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and i_lt: "i < unat data_pos"
      and data_le: "unat data_pos \<le> unat data_cap"
      and pend_lt: "pend_len < pending_cap"
  shows "data +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
proof -
  have disj: "bufs_disjoint data (unat data_cap) pending (unat pending_cap)"
    using ok by (simp add: encode_window_buffers_ok_def)
  have p_lt: "unat pend_len < unat pending_cap"
    using pend_lt by (simp add: word_less_nat_alt)
  have i_cap: "i < unat data_cap"
    using i_lt data_le by simp
  have ne: "data +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
    using disj i_cap p_lt
    unfolding bufs_disjoint_def by blast
  thus ?thesis
    by (subst uint_nat)
qed

lemma encode_window_buffers_ok_inst_pending_disj:
  assumes ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and i_lt: "i < unat inst_pos"
      and inst_le: "unat inst_pos \<le> unat inst_cap"
      and pend_lt: "pend_len < pending_cap"
  shows "inst +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
proof -
  have disj: "bufs_disjoint inst (unat inst_cap) pending (unat pending_cap)"
    using ok by (simp add: encode_window_buffers_ok_def)
  have p_lt: "unat pend_len < unat pending_cap"
    using pend_lt by (simp add: word_less_nat_alt)
  have i_cap: "i < unat inst_cap"
    using i_lt inst_le by simp
  have ne: "inst +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
    using disj i_cap p_lt
    unfolding bufs_disjoint_def by blast
  thus ?thesis
    by (subst uint_nat)
qed

lemma encode_window_buffers_ok_addr_pending_disj:
  assumes ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and i_lt: "i < unat addr_pos"
      and addr_le: "unat addr_pos \<le> unat addr_cap"
      and pend_lt: "pend_len < pending_cap"
  shows "addr +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
proof -
  have disj: "bufs_disjoint addr (unat addr_cap) pending (unat pending_cap)"
    using ok by (simp add: encode_window_buffers_ok_def)
  have p_lt: "unat pend_len < unat pending_cap"
    using pend_lt by (simp add: word_less_nat_alt)
  have i_cap: "i < unat addr_cap"
    using i_lt addr_le by simp
  have ne: "addr +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
    using disj i_cap p_lt
    unfolding bufs_disjoint_def by blast
  thus ?thesis
    by (subst uint_nat)
qed

definition encode_window_c_loop_result_inv ::
  "8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow>
   (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word) xval \<Rightarrow>
   lifted_globals \<Rightarrow> bool" where
  "encode_window_c_loop_result_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes rv st \<longleftrightarrow>
     (case rv of
       Exn sec \<Rightarrow> sections_t_C.err_C sec \<noteq> ENC_OK
     | Result (pend_len, sec, tp) \<Rightarrow>
         (\<exists>data_bytes inst_bytes addr_bytes flushed pending_bytes c_out.
           encode_window_c_loop_cache_inv st
             src src_len tgt tgt_len head_p next_p
             data data_cap inst inst_cap addr addr_cap
             pending pending_cap sec tp pend_len
             src_seg tgt_bytes data_bytes inst_bytes addr_bytes
             flushed pending_bytes c_out))"

definition encode_window_c_loop_run_inv ::
  "8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow>
   (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word) xval \<Rightarrow>
   lifted_globals \<Rightarrow> bool" where
  "encode_window_c_loop_run_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes rv st \<longleftrightarrow>
     encode_window_c_loop_result_inv
       src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
       pending pending_cap src_seg tgt_bytes rv st \<and>
     encode_window_buffers_ok st
       src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
       pending pending_cap \<and>
     encode_window_match_ok st src src_len tgt tgt_len head_p next_p
       src_seg tgt_bytes"

lemma encode_window_c_loop_result_inv_ResultI:
  assumes "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes flushed pending_bytes c_out"
  shows "encode_window_c_loop_result_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes (Result (pend_len, sec, tp)) st"
  using assms by (fastforce simp: encode_window_c_loop_result_inv_def)

lemma encode_window_c_loop_result_inv_ExnI:
  assumes "sections_t_C.err_C sec \<noteq> ENC_OK"
  shows "encode_window_c_loop_result_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes (Exn sec) st"
  using assms by (simp add: encode_window_c_loop_result_inv_def)

lemma encode_window_c_loop_result_inv_ResultD:
  assumes inv: "encode_window_c_loop_result_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes (Result (pend_len, sec, tp)) st"
  obtains data_bytes inst_bytes addr_bytes flushed pending_bytes c_out where
    "encode_window_c_loop_cache_inv st
       src src_len tgt tgt_len head_p next_p
       data data_cap inst inst_cap addr addr_cap
       pending pending_cap sec tp pend_len
       src_seg tgt_bytes data_bytes inst_bytes addr_bytes
       flushed pending_bytes c_out"
  using inv by (auto simp: encode_window_c_loop_result_inv_def)

lemma encode_window_c_loop_inv_entry:
  assumes sec: "sections_result sec 0 0 0 ENC_OK"
      and src_len: "length src_seg = unat src_len"
      and tgt_len: "length tgt_bytes = unat tgt_len"
      and src_heap: "heap_bytes st src (length src_seg) = src_seg"
      and tgt_heap: "heap_bytes st tgt (length tgt_bytes) = tgt_bytes"
  shows "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec 0 0
     src_seg tgt_bytes [] [] [] [] [] cache_init"
proof -
  have sec_fields:
    "sections_t_C.data_pos_C sec = 0"
    "sections_t_C.inst_pos_C sec = 0"
    "sections_t_C.addr_pos_C sec = 0"
    "sections_t_C.err_C sec = ENC_OK"
    using sections_resultD[OF sec] by simp_all
  show ?thesis
    using src_len tgt_len src_heap tgt_heap sec_fields
          enc_sections_inv_empty[of sec st data inst addr src_seg "length tgt_bytes"]
    by (simp add: encode_window_c_loop_inv_def heap_bytes_def)
qed

lemma encode_window_c_loop_cache_inv_entry:
  assumes sec: "sections_result sec 0 0 0 ENC_OK"
      and src_len: "length src_seg = unat src_len"
      and tgt_len: "length tgt_bytes = unat tgt_len"
      and src_heap: "heap_bytes st src (length src_seg) = src_seg"
      and tgt_heap: "heap_bytes st tgt (length tgt_bytes) = tgt_bytes"
      and cache_abs: "enc_cache_abs st cache_init"
      and cache_wf: "enc_cache_wf cache_init"
  shows "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec 0 0
     src_seg tgt_bytes [] [] [] [] [] cache_init"
  using encode_window_c_loop_inv_entry[OF sec src_len tgt_len src_heap tgt_heap]
        cache_abs cache_wf
  by (simp add: encode_window_c_loop_cache_inv_def)

lemma cache_reset'_enc_cache_abs_preserves2:
  fixes buf1 buf2 :: "8 word ptr"
    and n1 n2 :: nat
  shows "cache_reset' \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               enc_cache_abs t cache_init \<and>
               enc_cache_wf cache_init \<and>
               heap_typing t = heap_typing s \<and>
               heap_bytes t buf1 n1 = heap_bytes s buf1 n1 \<and>
               heap_bytes t buf2 n2 = heap_bytes s buf2 n2 \<rbrace>"
proof -
  have first:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           enc_cache_abs t cache_init \<and>
           enc_cache_wf cache_init \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t buf1 n1 = heap_bytes s buf1 n1 \<rbrace>"
    by (rule cache_reset'_enc_cache_abs)
  have second:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           enc_cache_abs t cache_init \<and>
           enc_cache_wf cache_init \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t buf2 n2 = heap_bytes s buf2 n2 \<rbrace>"
    by (rule cache_reset'_enc_cache_abs)
  have combined:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t.
          (r = Result () \<and>
           enc_cache_abs t cache_init \<and>
           enc_cache_wf cache_init \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t buf1 n1 = heap_bytes s buf1 n1) \<and>
          (r = Result () \<and>
           enc_cache_abs t cache_init \<and>
           enc_cache_wf cache_init \<and>
           heap_typing t = heap_typing s \<and>
           heap_bytes t buf2 n2 = heap_bytes s buf2 n2) \<rbrace>"
    using first second by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by auto
qed

lemma cache_reset'_encode_window_c_loop_cache_inv_entry:
  assumes src_len: "length src_seg = unat src_len"
      and tgt_len: "length tgt_bytes = unat tgt_len"
      and src_heap: "heap_bytes s src (length src_seg) = src_seg"
      and tgt_heap: "heap_bytes s tgt (length tgt_bytes) = tgt_bytes"
  shows "cache_reset' \<bullet> s
           \<lbrace> \<lambda>r t. r = Result () \<and>
               encode_window_c_loop_cache_inv t
                 src src_len tgt tgt_len head_p next_p
                 data data_cap inst inst_cap addr addr_cap
                 pending pending_cap (sections_t_C 0 0 0 0) 0 0
                 src_seg tgt_bytes [] [] [] [] [] cache_init \<and>
               heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF cache_reset'_enc_cache_abs_preserves2
      [of s src "length src_seg" tgt "length tgt_bytes"]])
  using src_len tgt_len src_heap tgt_heap
        encode_window_c_loop_cache_inv_entry
        [where sec = "sections_t_C 0 0 0 0" and st = _]
  by (auto simp: sections_result_def)

lemma encode_window_c_loop_cache_inv_pending_byte_step:
  assumes inv: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
      and tp_lt: "tp < tgt_len"
      and pend_lt: "pend_len < pending_cap"
      and pending_dist: "ptr_range_distinct pending (Suc (unat pend_len))"
      and src_disj:
        "\<forall>i < length src_seg.
           src +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      and tgt_disj:
        "\<forall>i < length tgt_bytes.
           tgt +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      and data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      and inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec).
           inst +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      and addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
  shows "encode_window_c_loop_cache_inv
     (heap_w8_update
        (\<lambda>h. h(pending +\<^sub>p int (unat pend_len) := tgt_bytes ! unat tp)) st)
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec (tp + 1) (pend_len + 1)
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed (pending_bytes @ [tgt_bytes ! unat tp]) c_out"
proof -
  let ?st' = "heap_w8_update
        (\<lambda>h. h(pending +\<^sub>p int (unat pend_len) := tgt_bytes ! unat tp)) st"
  have base: "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
    by (rule encode_window_c_loop_cache_invD(1)[OF inv])
  have abs: "enc_cache_abs st c_out"
    by (rule encode_window_c_loop_cache_invD(2)[OF inv])
  have cache_wf: "enc_cache_wf c_out"
    by (rule encode_window_c_loop_cache_invD(3)[OF inv])
  have pend_suc: "unat (pend_len + 1) = Suc (unat pend_len)"
    using pend_lt by (rule unat_word_suc_of_less)
  have pend_le: "unat (pend_len + 1) \<le> unat pending_cap"
    using pend_lt by (rule unat_suc_le_of_word_less)
  have src_heap:
    "heap_bytes ?st' src (length src_seg) = src_seg"
    using encode_window_c_loop_invD(4)[OF base] src_disj
    by (simp add: heap_bytes_update_outside)
  have tgt_heap:
    "heap_bytes ?st' tgt (length tgt_bytes) = tgt_bytes"
    using encode_window_c_loop_invD(5)[OF base] tgt_disj
    by (simp add: heap_bytes_update_outside)
  have pending_heap_suc:
    "heap_bytes ?st' pending (Suc (unat pend_len)) =
       heap_bytes st pending (unat pend_len) @ [tgt_bytes ! unat tp]"
    using heap_bytes_extend_distinct
      [OF pending_dist, of "tgt_bytes ! unat tp" st]
    by simp
  have pending_heap:
    "heap_bytes ?st' pending (unat (pend_len + 1)) =
       pending_bytes @ [tgt_bytes ! unat tp]"
    using encode_window_c_loop_invD(6,7)[OF base] pending_heap_suc
    by (simp add: pend_suc)
  have loop:
    "encoder_loop_inv tgt_bytes (unat (tp + 1)) flushed
       (pending_bytes @ [tgt_bytes ! unat tp])"
    using encoder_loop_inv_pending_step_word
      [OF encode_window_c_loop_invD(12)[OF base] tp_lt
          encode_window_c_loop_invD(3)[OF base]] .
  have sections:
    "enc_sections_inv ?st' data inst addr sec src_seg (length tgt_bytes)
       data_bytes inst_bytes addr_bytes flushed c_out"
    using encode_window_c_loop_invD(13)[OF base] data_disj inst_disj addr_disj
    by (auto simp: enc_sections_inv_def emitted_sections_def
        heap_bytes_update_outside)
  show ?thesis
    using base abs cache_wf pend_suc pend_le src_heap tgt_heap pending_heap loop sections
    by (simp add: encode_window_c_loop_cache_inv_def
        encode_window_c_loop_inv_def)
qed

lemma encode_window_c_loop_cache_inv_pending_byte_step_c_update:
  assumes inv: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
      and tp_lt: "tp < tgt_len"
      and pend_lt: "pend_len < pending_cap"
      and pending_dist: "ptr_range_distinct pending (Suc (unat pend_len))"
      and src_disj:
        "\<forall>i < length src_seg.
           src +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      and tgt_disj:
        "\<forall>i < length tgt_bytes.
           tgt +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      and data_disj:
        "\<forall>i < unat (sections_t_C.data_pos_C sec).
           data +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      and inst_disj:
        "\<forall>i < unat (sections_t_C.inst_pos_C sec).
           inst +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      and addr_disj:
        "\<forall>i < unat (sections_t_C.addr_pos_C sec).
           addr +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
  shows "encode_window_c_loop_cache_inv
     (heap_w8_update
        (\<lambda>h. h(pending +\<^sub>p uint pend_len := h (tgt +\<^sub>p uint tp))) st)
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec (tp + 1) (pend_len + 1)
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed (pending_bytes @ [tgt_bytes ! unat tp]) c_out"
proof -
  have base: "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
    by (rule encode_window_c_loop_cache_invD(1)[OF inv])
  have pend_ptr:
    "pending +\<^sub>p uint pend_len =
     pending +\<^sub>p int (unat pend_len)"
    by (simp only: uint_nat)
  have tgt_ptr:
    "tgt +\<^sub>p uint tp = tgt +\<^sub>p int (unat tp)"
    by (simp only: uint_nat)
  have tp_nat_lt: "unat tp < length tgt_bytes"
    using tp_lt encode_window_c_loop_invD(3)[OF base]
    by (simp add: word_less_nat_alt)
  have tgt_byte:
    "heap_w8 st (tgt +\<^sub>p uint tp) = tgt_bytes ! unat tp"
  proof -
    have "heap_w8 st (tgt +\<^sub>p uint tp) =
        heap_w8 st (tgt +\<^sub>p int (unat tp))"
      by (simp only: tgt_ptr)
    also have "... = heap_bytes st tgt (length tgt_bytes) ! unat tp"
      using heap_bytes_nth[OF tp_nat_lt, of st tgt] by simp
    also have "... = tgt_bytes ! unat tp"
      using encode_window_c_loop_invD(5)[OF base] by simp
    finally show ?thesis .
  qed
  have update_eq:
    "heap_w8_update
       (\<lambda>h. h(pending +\<^sub>p uint pend_len := h (tgt +\<^sub>p uint tp))) st =
     heap_w8_update
       (\<lambda>h. h(pending +\<^sub>p int (unat pend_len) :=
          tgt_bytes ! unat tp)) st"
  proof -
    have heap_fun_eq:
      "(\<lambda>h. h(pending +\<^sub>p uint pend_len := h (tgt +\<^sub>p uint tp))) (heap_w8 st) =
       (\<lambda>h. h(pending +\<^sub>p int (unat pend_len) :=
          tgt_bytes ! unat tp)) (heap_w8 st)"
      by (intro ext) (simp only: pend_ptr tgt_byte fun_upd_apply)
    show ?thesis
      using heap_fun_eq by simp
  qed
  have src_disj_int:
    "\<forall>i < length src_seg.
       src +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
  proof (intro allI impI)
    fix i
    assume "i < length src_seg"
    hence "src +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      using src_disj by blast
    thus "src +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      by (subst pend_ptr[symmetric])
  qed
  have tgt_disj_int:
    "\<forall>i < length tgt_bytes.
       tgt +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
  proof (intro allI impI)
    fix i
    assume "i < length tgt_bytes"
    hence "tgt +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      using tgt_disj by blast
    thus "tgt +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      by (subst pend_ptr[symmetric])
  qed
  have data_disj_int:
    "\<forall>i < unat (sections_t_C.data_pos_C sec).
       data +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
  proof (intro allI impI)
    fix i
    assume "i < unat (sections_t_C.data_pos_C sec)"
    hence "data +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      using data_disj by blast
    thus "data +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      by (subst pend_ptr[symmetric])
  qed
  have inst_disj_int:
    "\<forall>i < unat (sections_t_C.inst_pos_C sec).
       inst +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
  proof (intro allI impI)
    fix i
    assume "i < unat (sections_t_C.inst_pos_C sec)"
    hence "inst +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      using inst_disj by blast
    thus "inst +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      by (subst pend_ptr[symmetric])
  qed
  have addr_disj_int:
    "\<forall>i < unat (sections_t_C.addr_pos_C sec).
       addr +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
  proof (intro allI impI)
    fix i
    assume "i < unat (sections_t_C.addr_pos_C sec)"
    hence "addr +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      using addr_disj by blast
    thus "addr +\<^sub>p int i \<noteq> pending +\<^sub>p int (unat pend_len)"
      by (subst pend_ptr[symmetric])
  qed
  have step:
    "encode_window_c_loop_cache_inv
       (heap_w8_update
          (\<lambda>h. h(pending +\<^sub>p int (unat pend_len) :=
             tgt_bytes ! unat tp)) st)
       src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
       pending pending_cap sec (tp + 1) (pend_len + 1)
       src_seg tgt_bytes data_bytes inst_bytes addr_bytes
       flushed (pending_bytes @ [tgt_bytes ! unat tp]) c_out"
    by (rule encode_window_c_loop_cache_inv_pending_byte_step
      [OF inv tp_lt pend_lt pending_dist src_disj_int tgt_disj_int
          data_disj_int inst_disj_int addr_disj_int])
  show ?thesis
    using step by (simp only: update_eq)
qed

lemma encode_window_pending_byte_branch_result_inv:
  assumes inv: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
      and ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and tp_lt: "tp < tgt_len"
      and pend_lt: "pend_len < pending_cap"
  shows "(liftE (do {
            guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
            guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
            modify
              (heap_w8_update
                (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                       h (tgt +\<^sub>p uint tp))));
            return (pend_len + 1, sec, tp + 1)
          }) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                 lifted_globals) exn_monad) \<bullet> st
         \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t \<rbrace>"
proof -
  have base: "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
    by (rule encode_window_c_loop_cache_invD(1)[OF inv])
  have pending_ptr:
    "ptr_valid (heap_typing st) (pending +\<^sub>p uint pend_len)"
  proof -
    have valid: "buf_valid st pending (unat pending_cap)"
      using ok by (simp add: encode_window_buffers_ok_def)
    have p_lt: "unat pend_len < unat pending_cap"
      using pend_lt by (simp add: word_less_nat_alt)
    have "ptr_valid (heap_typing st) (pending +\<^sub>p int (unat pend_len))"
      by (rule buf_validD[OF valid p_lt])
    thus ?thesis
      by (subst uint_nat)
  qed
  have tgt_ptr: "ptr_valid (heap_typing st) (tgt +\<^sub>p uint tp)"
  proof -
    have valid: "buf_valid st tgt (unat tgt_len)"
      using ok by (simp add: encode_window_buffers_ok_def)
    have p_lt: "unat tp < unat tgt_len"
      using tp_lt by (simp add: word_less_nat_alt)
    have "ptr_valid (heap_typing st) (tgt +\<^sub>p int (unat tp))"
      by (rule buf_validD[OF valid p_lt])
    thus ?thesis
      by (subst uint_nat)
  qed
  have pending_dist:
    "ptr_range_distinct pending (Suc (unat pend_len))"
    by (rule encode_window_buffers_ok_pending_dist[OF ok pend_lt])
  have src_disj:
    "\<forall>i < length src_seg. src +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length src_seg"
    have "i < unat src_len"
      using i_lt encode_window_c_loop_invD(2)[OF base] by simp
    thus "src +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      by (rule encode_window_buffers_ok_src_pending_disj[OF ok _ pend_lt])
  qed
  have tgt_disj:
    "\<forall>i < length tgt_bytes. tgt +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length tgt_bytes"
    have "i < unat tgt_len"
      using i_lt encode_window_c_loop_invD(3)[OF base] by simp
    thus "tgt +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      by (rule encode_window_buffers_ok_tgt_pending_disj[OF ok _ pend_lt])
  qed
  have data_disj:
    "\<forall>i < unat (sections_t_C.data_pos_C sec).
       data +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < unat (sections_t_C.data_pos_C sec)"
    show "data +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      by (rule encode_window_buffers_ok_data_pending_disj
        [OF ok i_lt encode_window_c_loop_invD(9)[OF base] pend_lt])
  qed
  have inst_disj:
    "\<forall>i < unat (sections_t_C.inst_pos_C sec).
       inst +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < unat (sections_t_C.inst_pos_C sec)"
    show "inst +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      by (rule encode_window_buffers_ok_inst_pending_disj
        [OF ok i_lt encode_window_c_loop_invD(10)[OF base] pend_lt])
  qed
  have addr_disj:
    "\<forall>i < unat (sections_t_C.addr_pos_C sec).
       addr +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < unat (sections_t_C.addr_pos_C sec)"
    show "addr +\<^sub>p int i \<noteq> pending +\<^sub>p uint pend_len"
      by (rule encode_window_buffers_ok_addr_pending_disj
        [OF ok i_lt encode_window_c_loop_invD(11)[OF base] pend_lt])
  qed
  have step:
    "encode_window_c_loop_cache_inv
       (heap_w8_update
          (\<lambda>h. h(pending +\<^sub>p uint pend_len := h (tgt +\<^sub>p uint tp))) st)
       src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
       pending pending_cap sec (tp + 1) (pend_len + 1)
       src_seg tgt_bytes data_bytes inst_bytes addr_bytes
       flushed (pending_bytes @ [tgt_bytes ! unat tp]) c_out"
    by (rule encode_window_c_loop_cache_inv_pending_byte_step_c_update
      [OF inv tp_lt pend_lt pending_dist src_disj tgt_disj data_disj
          inst_disj addr_disj])
  show ?thesis
    apply runs_to_vcg
      apply (rule pending_ptr)
     apply (rule tgt_ptr)
    by (rule encode_window_c_loop_result_inv_ResultI[OF step])
qed

lemma encode_window_pending_byte_branch_result_shape:
  assumes ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and tp_lt: "tp < tgt_len"
      and pend_lt: "pend_len < pending_cap"
  shows "(liftE (do {
            guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
            guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
            modify
              (heap_w8_update
                (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                       h (tgt +\<^sub>p uint tp))));
            return (pend_len + 1, sec, tp + 1)
          }) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                 lifted_globals) exn_monad) \<bullet> st
         \<lbrace> \<lambda>r t. r = Result (pend_len + 1, sec, tp + 1) \<rbrace>"
proof -
  have pending_ptr:
    "ptr_valid (heap_typing st) (pending +\<^sub>p uint pend_len)"
  proof -
    have valid: "buf_valid st pending (unat pending_cap)"
      using ok by (simp add: encode_window_buffers_ok_def)
    have p_lt: "unat pend_len < unat pending_cap"
      using pend_lt by (simp add: word_less_nat_alt)
    have "ptr_valid (heap_typing st) (pending +\<^sub>p int (unat pend_len))"
      by (rule buf_validD[OF valid p_lt])
    thus ?thesis
      by (subst uint_nat)
  qed
  have tgt_ptr: "ptr_valid (heap_typing st) (tgt +\<^sub>p uint tp)"
  proof -
    have valid: "buf_valid st tgt (unat tgt_len)"
      using ok by (simp add: encode_window_buffers_ok_def)
    have p_lt: "unat tp < unat tgt_len"
      using tp_lt by (simp add: word_less_nat_alt)
    have "ptr_valid (heap_typing st) (tgt +\<^sub>p int (unat tp))"
      by (rule buf_validD[OF valid p_lt])
    thus ?thesis
      by (subst uint_nat)
  qed
  show ?thesis
    apply runs_to_vcg
      apply (rule pending_ptr)
     apply (rule tgt_ptr)
    done
qed

lemma encode_window_pending_byte_branch_loop_step:
  assumes inv: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
      and ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and tp_lt: "tp < tgt_len"
      and pend_lt: "pend_len < pending_cap"
  shows "(liftE (do {
            guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
            guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
            modify
              (heap_w8_update
                (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                       h (tgt +\<^sub>p uint tp))));
            return (pend_len + 1, sec, tp + 1)
          }) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                 lifted_globals) exn_monad) \<bullet> st
         \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t \<and>
            (\<forall>b. r = Result b \<longrightarrow>
              ((b, t), ((pend_len, sec, tp), st)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp)) \<rbrace>"
proof -
  have inv_post:
    "(liftE (do {
            guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
            guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
            modify
              (heap_w8_update
                (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                       h (tgt +\<^sub>p uint tp))));
            return (pend_len + 1, sec, tp + 1)
          }) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                 lifted_globals) exn_monad) \<bullet> st
       \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t \<rbrace>"
    by (rule encode_window_pending_byte_branch_result_inv
      [OF inv ok tp_lt pend_lt])
  have shape_post:
    "(liftE (do {
            guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
            guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
            modify
              (heap_w8_update
                (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                       h (tgt +\<^sub>p uint tp))));
            return (pend_len + 1, sec, tp + 1)
          }) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                 lifted_globals) exn_monad) \<bullet> st
       \<lbrace> \<lambda>r t. r = Result (pend_len + 1, sec, tp + 1) \<rbrace>"
    by (rule encode_window_pending_byte_branch_result_shape
      [OF ok tp_lt pend_lt])
  have combined:
    "(liftE (do {
            guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
            guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
            modify
              (heap_w8_update
                (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                       h (tgt +\<^sub>p uint tp))));
            return (pend_len + 1, sec, tp + 1)
          }) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                 lifted_globals) exn_monad) \<bullet> st
       \<lbrace> \<lambda>r t.
          encode_window_c_loop_result_inv
            src src_len tgt tgt_len head_p next_p
            data data_cap inst inst_cap addr addr_cap
            pending pending_cap src_seg tgt_bytes r t \<and>
          r = Result (pend_len + 1, sec, tp + 1) \<rbrace>"
    using inv_post shape_post by (simp add: runs_to_conj)
  have suc: "unat (tp + 1) = Suc (unat tp)"
    using tp_lt by (rule unat_word_suc_of_less)
  have tp_nat_lt: "unat tp < unat tgt_len"
    using tp_lt by (simp add: word_less_nat_alt)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    using suc tp_nat_lt by auto
qed

lemma runs_to_condition_exnI:
  assumes "c s \<Longrightarrow> (f :: ('e, 'a, 's) exn_monad) \<bullet> s \<lbrace>Q\<rbrace>"
      and "\<not> c s \<Longrightarrow> (g :: ('e, 'a, 's) exn_monad) \<bullet> s \<lbrace>Q\<rbrace>"
  shows "condition c f g \<bullet> s \<lbrace>Q\<rbrace>"
  unfolding condition_def
  apply runs_to_vcg
  using assms by simp_all

lemma encode_window_pending_match_branch_result_inv:
  assumes inv: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
      and ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and tp_lt: "tp < tgt_len"
  shows "(condition (\<lambda>s. pending_cap \<le> pend_len)
            (throw (sections_t_C.err_C_update (\<lambda>_. 1) sec))
            (liftE (do {
              guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
              guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
              modify
                (heap_w8_update
                  (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                         h (tgt +\<^sub>p uint tp))));
              return (pend_len + 1, sec, tp + 1)
            })) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                    lifted_globals) exn_monad) \<bullet> st
         \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t \<rbrace>"
proof (rule runs_to_condition_exnI)
  assume "(\<lambda>s. pending_cap \<le> pend_len) st"
  show "(throw (sections_t_C.err_C_update (\<lambda>_. 1) sec) ::
          (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
           lifted_globals) exn_monad) \<bullet> st
        \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
             src src_len tgt tgt_len head_p next_p
             data data_cap inst inst_cap addr addr_cap
             pending pending_cap src_seg tgt_bytes r t \<rbrace>"
    apply runs_to_vcg
    by (rule encode_window_c_loop_result_inv_ExnI) simp
next
  assume not_full: "\<not> (\<lambda>s. pending_cap \<le> pend_len) st"
  have pend_lt: "pend_len < pending_cap"
    using not_full by simp
  show "(liftE (do {
              guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
              guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
              modify
                (heap_w8_update
                  (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                         h (tgt +\<^sub>p uint tp))));
              return (pend_len + 1, sec, tp + 1)
            }) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                    lifted_globals) exn_monad) \<bullet> st
        \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
             src src_len tgt tgt_len head_p next_p
             data data_cap inst inst_cap addr addr_cap
             pending pending_cap src_seg tgt_bytes r t \<rbrace>"
    by (rule encode_window_pending_byte_branch_result_inv
      [OF inv ok tp_lt pend_lt])
qed

lemma encode_window_pending_match_branch_loop_step:
  assumes inv: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
      and ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and tp_lt: "tp < tgt_len"
  shows "(condition (\<lambda>s. pending_cap \<le> pend_len)
            (throw (sections_t_C.err_C_update (\<lambda>_. 1) sec))
            (liftE (do {
              guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
              guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
              modify
                (heap_w8_update
                  (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                         h (tgt +\<^sub>p uint tp))));
              return (pend_len + 1, sec, tp + 1)
            })) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                    lifted_globals) exn_monad) \<bullet> st
         \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t \<and>
            (\<forall>b. r = Result b \<longrightarrow>
              ((b, t), ((pend_len, sec, tp), st)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp)) \<rbrace>"
proof (rule runs_to_condition_exnI)
  assume "(\<lambda>s. pending_cap \<le> pend_len) st"
  show "(throw (sections_t_C.err_C_update (\<lambda>_. 1) sec) ::
          (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
           lifted_globals) exn_monad) \<bullet> st
        \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
             src src_len tgt tgt_len head_p next_p
             data data_cap inst inst_cap addr addr_cap
             pending pending_cap src_seg tgt_bytes r t \<and>
           (\<forall>b. r = Result b \<longrightarrow>
             ((b, t), ((pend_len, sec, tp), st)) \<in>
               measure
                 (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                    unat tgt_len - unat tp)) \<rbrace>"
    apply runs_to_vcg
     apply (rule encode_window_c_loop_result_inv_ExnI)
     apply simp
    done
next
  assume not_full: "\<not> (\<lambda>s. pending_cap \<le> pend_len) st"
  have pend_lt: "pend_len < pending_cap"
    using not_full by simp
  show "(liftE (do {
              guard (\<lambda>s. IS_VALID(8 word) s (pending +\<^sub>p uint pend_len));
              guard (\<lambda>s. IS_VALID(8 word) s (tgt +\<^sub>p uint tp));
              modify
                (heap_w8_update
                  (\<lambda>h. h(pending +\<^sub>p uint pend_len :=
                         h (tgt +\<^sub>p uint tp))));
              return (pend_len + 1, sec, tp + 1)
            }) :: (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
                    lifted_globals) exn_monad) \<bullet> st
        \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
             src src_len tgt tgt_len head_p next_p
             data data_cap inst inst_cap addr addr_cap
             pending pending_cap src_seg tgt_bytes r t \<and>
           (\<forall>b. r = Result b \<longrightarrow>
             ((b, t), ((pend_len, sec, tp), st)) \<in>
               measure
                 (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                    unat tgt_len - unat tp)) \<rbrace>"
    by (rule encode_window_pending_byte_branch_loop_step
      [OF inv ok tp_lt pend_lt])
qed

lemma encode_window_c_loop_body_result_inv:
  assumes inv: "encode_window_c_loop_result_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes (Result (pend_len, sec, tp)) st"
      and ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and match_ok: "encode_window_match_ok st src src_len tgt tgt_len
     head_p next_p src_seg tgt_bytes"
      and tp_lt: "tp < tgt_len"
  shows "encode_window_c_loop_body
           src src_len tgt tgt_len head_p next_p
           data data_cap inst inst_cap addr addr_cap
           pending pending_cap (pend_len, sec, tp) \<bullet> st
         \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t \<and>
            (\<forall>b. r = Result b \<longrightarrow>
              ((b, t), ((pend_len, sec, tp), st)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp)) \<rbrace>"
proof -
  obtain data_bytes inst_bytes addr_bytes flushed pending_bytes c_out where loop:
    "encode_window_c_loop_cache_inv st
       src src_len tgt tgt_len head_p next_p
       data data_cap inst inst_cap addr addr_cap
       pending pending_cap sec tp pend_len
       src_seg tgt_bytes data_bytes inst_bytes addr_bytes
       flushed pending_bytes c_out"
    by (rule encode_window_c_loop_result_inv_ResultD[OF inv])
  obtain m where find:
    "find_best_match' src src_len tgt tgt_len tp head_p next_p st = Some m"
    and match_valid:
    "match_valid src_seg tgt_bytes (unat tp)
       (unat (match_t_C.pos_C m)) (unat (match_t_C.len_C m))"
    by (rule encode_window_match_okD[OF match_ok tp_lt])
  show ?thesis
    unfolding encode_window_c_loop_body_def
    apply simp
    apply runs_to_vcg
    apply (rule exI[where x = m])
    apply (simp add: find)
    apply (rule runs_to_condition_exnI)
     apply (rule runs_to_weaken[
       OF encode_window_pending_match_branch_loop_step[OF loop ok tp_lt]])
     apply auto
    sorry
qed

lemma encode_window_c_loop_body_run_inv:
  assumes inv: "encode_window_c_loop_run_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes (Result (pend_len, sec, tp)) st"
      and tp_lt: "tp < tgt_len"
  shows "encode_window_c_loop_body
           src src_len tgt tgt_len head_p next_p
           data data_cap inst inst_cap addr addr_cap
           pending pending_cap (pend_len, sec, tp) \<bullet> st
         \<lbrace> \<lambda>r t. encode_window_c_loop_run_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t \<and>
            (\<forall>b. r = Result b \<longrightarrow>
              ((b, t), ((pend_len, sec, tp), st)) \<in>
                measure
                  (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                     unat tgt_len - unat tp)) \<rbrace>"
proof -
  have result_inv:
    "encode_window_c_loop_result_inv
       src src_len tgt tgt_len head_p next_p
       data data_cap inst inst_cap addr addr_cap
       pending pending_cap src_seg tgt_bytes (Result (pend_len, sec, tp)) st"
    using inv by (simp add: encode_window_c_loop_run_inv_def)
  have bufs_ok:
    "encode_window_buffers_ok st
       src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
       pending pending_cap"
    using inv by (simp add: encode_window_c_loop_run_inv_def)
  have match_ok:
    "encode_window_match_ok st src src_len tgt tgt_len head_p next_p
       src_seg tgt_bytes"
    using inv by (simp add: encode_window_c_loop_run_inv_def)
  have result_step:
    "encode_window_c_loop_body
       src src_len tgt tgt_len head_p next_p
       data data_cap inst inst_cap addr addr_cap
       pending pending_cap (pend_len, sec, tp) \<bullet> st
     \<lbrace> \<lambda>r t. encode_window_c_loop_result_inv
          src src_len tgt tgt_len head_p next_p
          data data_cap inst inst_cap addr addr_cap
          pending pending_cap src_seg tgt_bytes r t \<and>
        (\<forall>b. r = Result b \<longrightarrow>
          ((b, t), ((pend_len, sec, tp), st)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp)) \<rbrace>"
    by (rule encode_window_c_loop_body_result_inv
      [OF result_inv bufs_ok match_ok tp_lt])
  have aux_step:
    "encode_window_c_loop_body
       src src_len tgt tgt_len head_p next_p
       data data_cap inst inst_cap addr addr_cap
       pending pending_cap (pend_len, sec, tp) \<bullet> st
     \<lbrace> \<lambda>r t. encode_window_buffers_ok t
          src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
          pending pending_cap \<and>
        encode_window_match_ok t src src_len tgt tgt_len head_p next_p
          src_seg tgt_bytes \<rbrace>"
    sorry
  have combined:
    "encode_window_c_loop_body
       src src_len tgt tgt_len head_p next_p
       data data_cap inst inst_cap addr addr_cap
       pending pending_cap (pend_len, sec, tp) \<bullet> st
     \<lbrace> \<lambda>r t.
        (encode_window_c_loop_result_inv
          src src_len tgt tgt_len head_p next_p
          data data_cap inst inst_cap addr addr_cap
          pending pending_cap src_seg tgt_bytes r t \<and>
         (\<forall>b. r = Result b \<longrightarrow>
          ((b, t), ((pend_len, sec, tp), st)) \<in>
            measure
              (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
                 unat tgt_len - unat tp))) \<and>
        (encode_window_buffers_ok t
          src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
          pending pending_cap \<and>
         encode_window_match_ok t src src_len tgt tgt_len head_p next_p
          src_seg tgt_bytes) \<rbrace>"
    using result_step aux_step by (simp add: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF combined])
    by (auto simp: encode_window_c_loop_run_inv_def)
qed

lemma encode_window_c_loop_while_run_inv:
  assumes init: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec0 0 0
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
      and bufs_ok: "encode_window_buffers_ok st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap"
      and match_ok: "encode_window_match_ok st src src_len tgt tgt_len
     head_p next_p src_seg tgt_bytes"
  shows "(whileLoop (\<lambda>(pend_len, sec, tp) s. tp < tgt_len)
           (encode_window_c_loop_body
             src src_len tgt tgt_len head_p next_p
             data data_cap inst inst_cap addr addr_cap
             pending pending_cap)
           (0, sec0, 0) ::
          (sections_t_C, 32 word \<times> sections_t_C \<times> 32 word,
           lifted_globals) exn_monad) \<bullet> st
         \<lbrace> \<lambda>r t. encode_window_c_loop_run_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t \<and>
            (\<forall>pend_len sec tp.
              r = Result (pend_len, sec, tp) \<longrightarrow> \<not> tp < tgt_len) \<rbrace>"
  apply (rule runs_to_whileLoop_exn'[
    where R = "measure
      (\<lambda>((_ :: 32 word, _ :: sections_t_C, tp :: 32 word), _).
         unat tgt_len - unat tp)"
      and I = "\<lambda>r t. encode_window_c_loop_run_inv
              src src_len tgt tgt_len head_p next_p
              data data_cap inst inst_cap addr addr_cap
              pending pending_cap src_seg tgt_bytes r t"])
      apply (clarsimp split: prod.splits)
      apply (rule runs_to_weaken)
       apply (rule encode_window_c_loop_body_run_inv)
        apply assumption
       apply assumption
      apply auto
     apply (simp add: encode_window_c_loop_run_inv_def)
     apply (rule conjI)
      apply (rule encode_window_c_loop_result_inv_ResultI[OF init])
     using bufs_ok match_ok by simp

lemma encode_window_c_loop_result_inv_doneD:
  assumes inv: "encode_window_c_loop_result_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes (Result (0, sec, tp)) st"
      and exit: "\<not> tp < tgt_len"
  shows "\<exists>data_bytes inst_bytes addr_bytes c_out.
     enc_sections_inv st data inst addr sec src_seg (length tgt_bytes)
       data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
     enc_cache_abs st c_out \<and>
     enc_cache_wf c_out"
proof -
  obtain data_bytes inst_bytes addr_bytes flushed pending_bytes c_out where loop:
    "encode_window_c_loop_cache_inv st
       src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
       pending pending_cap sec tp 0
       src_seg tgt_bytes data_bytes inst_bytes addr_bytes flushed pending_bytes c_out"
    using inv by (auto simp: encode_window_c_loop_result_inv_def)
  have base: "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp 0
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
    by (rule encode_window_c_loop_cache_invD(1)[OF loop])
  have tp_le: "unat tp \<le> unat tgt_len"
    by (rule encode_window_c_loop_inv_tp_le_tgt_len[OF base])
  have tgt_le: "unat tgt_len \<le> unat tp"
    using exit by (simp add: word_less_nat_alt)
  have tp_done: "tp = tgt_len"
    using tp_le tgt_le by (metis antisym word_unat.Rep_inject)
  have pending_empty: "pending_bytes = []"
    using encode_window_c_loop_invD(7)[OF base] by simp
  have flushed_eq: "flushed = tgt_bytes"
    using encode_window_c_loop_invD(3,12)[OF base] tp_done pending_empty
          encoder_loop_inv_done_no_pendingD
    by fastforce
  have sections:
    "enc_sections_inv st data inst addr sec src_seg (length tgt_bytes)
      data_bytes inst_bytes addr_bytes tgt_bytes c_out"
    using encode_window_c_loop_invD(13)[OF base] flushed_eq by simp
  have abs: "enc_cache_abs st c_out"
    by (rule encode_window_c_loop_cache_invD(2)[OF loop])
  have wf: "enc_cache_wf c_out"
    by (rule encode_window_c_loop_cache_invD(3)[OF loop])
  show ?thesis
    using sections abs wf by blast
qed

definition encode_window_final_sections_cache_post ::
  "8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow>
   byte list \<Rightarrow> byte list \<Rightarrow>
   (sections_t_C, sections_t_C) xval \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "encode_window_final_sections_cache_post data inst addr src_seg tgt_bytes rv st \<longleftrightarrow>
     (case rv of
       Result sec \<Rightarrow>
         sections_t_C.err_C sec = ENC_OK \<longrightarrow>
         (\<exists>data_bytes inst_bytes addr_bytes c_out.
           enc_sections_inv st data inst addr sec src_seg (length tgt_bytes)
             data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
           enc_cache_abs st c_out \<and>
           enc_cache_wf c_out)
     | Exn sec \<Rightarrow>
         sections_t_C.err_C sec = ENC_OK \<longrightarrow>
         (\<exists>data_bytes inst_bytes addr_bytes c_out.
           enc_sections_inv st data inst addr sec src_seg (length tgt_bytes)
             data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
           enc_cache_abs st c_out \<and>
           enc_cache_wf c_out))"

lemma encode_window_c_loop_final_flush_zero:
  assumes run: "encode_window_c_loop_run_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes (Result (0, sec, tp)) st"
      and exit: "\<not> tp < tgt_len"
  shows "((liftE
            (condition (\<lambda>s. 0 < (0 :: 32 word))
              (flush_pending' sec data data_cap inst inst_cap pending 0)
              (return sec)) >>= throw) ::
         (sections_t_C, sections_t_C, lifted_globals) exn_monad) \<bullet> st
         \<lbrace> encode_window_final_sections_cache_post data inst addr
              src_seg tgt_bytes \<rbrace>"
  apply (simp add: condition_def encode_window_final_sections_cache_post_def)
  apply runs_to_vcg
  using assms encode_window_c_loop_result_inv_doneD
  by (fastforce simp: encode_window_c_loop_run_inv_def)

lemma encode_window_c_loop_final_flush_result:
  assumes run: "encode_window_c_loop_run_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes (Result (pend_len, sec, tp)) st"
      and exit: "\<not> tp < tgt_len"
  shows "((liftE
            (condition (\<lambda>s. 0 < pend_len)
              (flush_pending' sec data data_cap inst inst_cap pending pend_len)
              (return sec)) >>= throw) ::
          (sections_t_C, sections_t_C, lifted_globals) exn_monad) \<bullet> st
         \<lbrace> encode_window_final_sections_cache_post data inst addr
              src_seg tgt_bytes \<rbrace>"
  apply (cases "pend_len = 0")
   apply hypsubst
   apply (rule encode_window_c_loop_final_flush_zero
     [where src = src and src_len = src_len
        and tgt = tgt and tgt_len = tgt_len
        and head_p = head_p and next_p = next_p
        and addr_cap = addr_cap and pending_cap = pending_cap
        and tp = tp])
    apply (use run in simp)
   apply (use exit in simp)
  sorry

lemma encode_window_c_loop_final_flush_run_inv:
  assumes run: "encode_window_c_loop_run_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes r st"
      and exit:
        "\<forall>pend_len sec tp.
           r = Result (pend_len, sec, tp) \<longrightarrow> \<not> tp < tgt_len"
  shows "(\<forall>v. r = Result v \<longrightarrow>
            (case v of
              (pend_len, sec, tp) \<Rightarrow>
                liftE
                  (condition (\<lambda>s. 0 < pend_len)
                    (flush_pending' sec data data_cap inst inst_cap pending
                      pend_len)
                    (return sec)) >>= throw)
            \<bullet> st
            \<lbrace> encode_window_final_sections_cache_post data inst addr
                 src_seg tgt_bytes \<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
            encode_window_final_sections_cache_post data inst addr
              src_seg tgt_bytes (Exn e) st)"
proof (intro conjI allI impI)
  fix v
  assume r_result: "r = Result v"
  obtain pend_len sec tp where v: "v = (pend_len, sec, tp)"
    by (cases v) auto
  have run_result:
    "encode_window_c_loop_run_inv
       src src_len tgt tgt_len head_p next_p
       data data_cap inst inst_cap addr addr_cap
       pending pending_cap src_seg tgt_bytes
       (Result (pend_len, sec, tp)) st"
    using run r_result v by simp
  have exit_result: "\<not> tp < tgt_len"
    using exit r_result v by simp
  have final:
    "((liftE
          (condition (\<lambda>s. 0 < pend_len)
            (flush_pending' sec data data_cap inst inst_cap pending pend_len)
            (return sec)) >>= throw) ::
        (sections_t_C, sections_t_C, lifted_globals) exn_monad) \<bullet> st
       \<lbrace> encode_window_final_sections_cache_post data inst addr
            src_seg tgt_bytes \<rbrace>"
    by (rule encode_window_c_loop_final_flush_result[OF run_result exit_result])
  show "(case v of
          (pend_len, sec, tp) \<Rightarrow>
            liftE
              (condition (\<lambda>s. 0 < pend_len)
                (flush_pending' sec data data_cap inst inst_cap pending pend_len)
                (return sec)) >>= throw)
        \<bullet> st
        \<lbrace> encode_window_final_sections_cache_post data inst addr
             src_seg tgt_bytes \<rbrace>"
    using v final by simp
next
  fix e
  assume r_exn: "r = Exn e"
  have err: "sections_t_C.err_C e \<noteq> ENC_OK"
    using run r_exn
    by (simp add: encode_window_c_loop_run_inv_def
                  encode_window_c_loop_result_inv_def)
  show "encode_window_final_sections_cache_post data inst addr
          src_seg tgt_bytes (Exn e) st"
    using err by (simp add: encode_window_final_sections_cache_post_def)
qed

lemma encode_window_c_loop_final_flush_run_inv_generated:
  assumes run: "encode_window_c_loop_run_inv
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap src_seg tgt_bytes r st"
      and exit:
        "\<forall>pend_len sec tp.
           r = Result (pend_len, sec, tp) \<longrightarrow> \<not> tp < tgt_len"
  shows "(\<forall>pend_len sec.
            (\<exists>tp. r = Result (pend_len, sec, tp)) \<longrightarrow>
            ((liftE
                (condition (\<lambda>s. 0 < pend_len)
                  (flush_pending' sec data data_cap inst inst_cap pending
                    pend_len)
                  (return sec)) >>= throw) ::
              (sections_t_C, sections_t_C, lifted_globals) exn_monad) \<bullet> st
            \<lbrace> \<lambda>r t.
              (\<forall>sec. r = Result sec \<longrightarrow>
                sections_t_C.err_C sec = ENC_OK \<longrightarrow>
                (\<exists>data_bytes inst_bytes addr_bytes c_out.
                  enc_sections_inv t data inst addr sec src_seg
                    (length tgt_bytes) data_bytes inst_bytes addr_bytes
                    tgt_bytes c_out \<and>
                  enc_cache_abs t c_out \<and>
                  enc_cache_wf c_out)) \<and>
              (\<forall>sec. r = Exn sec \<longrightarrow>
                sections_t_C.err_C sec = ENC_OK \<longrightarrow>
                (\<exists>data_bytes inst_bytes addr_bytes c_out.
                  enc_sections_inv t data inst addr sec src_seg
                    (length tgt_bytes) data_bytes inst_bytes addr_bytes
                    tgt_bytes c_out \<and>
                  enc_cache_abs t c_out \<and>
                  enc_cache_wf c_out)) \<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
            sections_t_C.err_C e = ENC_OK \<longrightarrow>
            (\<exists>data_bytes inst_bytes addr_bytes c_out.
              enc_sections_inv st data inst addr e src_seg (length tgt_bytes)
                data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
              enc_cache_abs st c_out \<and>
              enc_cache_wf c_out))"
proof (intro conjI allI impI)
  fix pend_len sec
  assume "\<exists>tp. r = Result (pend_len, sec, tp)"
  then obtain tp where r_result: "r = Result (pend_len, sec, tp)"
    by blast
  have base:
    "(\<forall>v. r = Result v \<longrightarrow>
        (case v of
          (pend_len, sec, tp) \<Rightarrow>
            liftE
              (condition (\<lambda>s. 0 < pend_len)
                (flush_pending' sec data data_cap inst inst_cap pending
                  pend_len)
                (return sec)) >>= throw)
        \<bullet> st
        \<lbrace> encode_window_final_sections_cache_post data inst addr
             src_seg tgt_bytes \<rbrace>) \<and>
     (\<forall>e. r = Exn e \<longrightarrow>
        encode_window_final_sections_cache_post data inst addr
          src_seg tgt_bytes (Exn e) st)"
    by (rule encode_window_c_loop_final_flush_run_inv[OF run exit])
  have final:
    "((liftE
        (condition (\<lambda>s. 0 < pend_len)
          (flush_pending' sec data data_cap inst inst_cap pending pend_len)
          (return sec)) >>= throw) ::
      (sections_t_C, sections_t_C, lifted_globals) exn_monad) \<bullet> st
     \<lbrace> encode_window_final_sections_cache_post data inst addr
          src_seg tgt_bytes \<rbrace>"
    using base r_result by auto
  show "((liftE
          (condition (\<lambda>s. 0 < pend_len)
            (flush_pending' sec data data_cap inst inst_cap pending pend_len)
            (return sec)) >>= throw) ::
        (sections_t_C, sections_t_C, lifted_globals) exn_monad) \<bullet> st
       \<lbrace> \<lambda>r t.
          (\<forall>sec. r = Result sec \<longrightarrow>
            sections_t_C.err_C sec = ENC_OK \<longrightarrow>
            (\<exists>data_bytes inst_bytes addr_bytes c_out.
              enc_sections_inv t data inst addr sec src_seg
                (length tgt_bytes) data_bytes inst_bytes addr_bytes
                tgt_bytes c_out \<and>
              enc_cache_abs t c_out \<and>
              enc_cache_wf c_out)) \<and>
          (\<forall>sec. r = Exn sec \<longrightarrow>
            sections_t_C.err_C sec = ENC_OK \<longrightarrow>
            (\<exists>data_bytes inst_bytes addr_bytes c_out.
              enc_sections_inv t data inst addr sec src_seg
                (length tgt_bytes) data_bytes inst_bytes addr_bytes
                tgt_bytes c_out \<and>
              enc_cache_abs t c_out \<and>
              enc_cache_wf c_out)) \<rbrace>"
    apply (rule runs_to_weaken[OF final])
    by (auto simp: encode_window_final_sections_cache_post_def)
next
  fix e
  assume r_exn: "r = Exn e"
     and err_ok: "sections_t_C.err_C e = ENC_OK"
  have base:
    "(\<forall>v. r = Result v \<longrightarrow>
        (case v of
          (pend_len, sec, tp) \<Rightarrow>
            liftE
              (condition (\<lambda>s. 0 < pend_len)
                (flush_pending' sec data data_cap inst inst_cap pending
                  pend_len)
                (return sec)) >>= throw)
        \<bullet> st
        \<lbrace> encode_window_final_sections_cache_post data inst addr
             src_seg tgt_bytes \<rbrace>) \<and>
     (\<forall>e. r = Exn e \<longrightarrow>
        encode_window_final_sections_cache_post data inst addr
          src_seg tgt_bytes (Exn e) st)"
    by (rule encode_window_c_loop_final_flush_run_inv[OF run exit])
  have post:
    "encode_window_final_sections_cache_post data inst addr
       src_seg tgt_bytes (Exn e) st"
    using base r_exn by simp
  show "\<exists>data_bytes inst_bytes addr_bytes c_out.
          enc_sections_inv st data inst addr e src_seg (length tgt_bytes)
            data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
          enc_cache_abs st c_out \<and>
          enc_cache_wf c_out"
    using post err_ok by (simp add: encode_window_final_sections_cache_post_def)
qed

lemma encode_window_c_loop_cache_inv_doneD:
  assumes inv: "encode_window_c_loop_cache_inv st
     src src_len tgt tgt_len head_p next_p data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
      and tp_done: "tp = tgt_len"
      and pend_done: "pend_len = 0"
  shows "enc_sections_inv st data inst addr sec src_seg (length tgt_bytes)
           data_bytes inst_bytes addr_bytes tgt_bytes c_out"
    and "enc_cache_abs st c_out"
    and "enc_cache_wf c_out"
proof -
  have base: "encode_window_c_loop_inv st
     src src_len tgt tgt_len data data_cap inst inst_cap addr addr_cap
     pending pending_cap sec tp pend_len
     src_seg tgt_bytes data_bytes inst_bytes addr_bytes
     flushed pending_bytes c_out"
    by (rule encode_window_c_loop_cache_invD(1)[OF inv])
  have pending_empty: "pending_bytes = []"
    using encode_window_c_loop_invD(7)[OF base] pend_done by simp
  have flushed_eq: "flushed = tgt_bytes"
    using encode_window_c_loop_invD(3,12)[OF base] tp_done pending_empty
          encoder_loop_inv_done_no_pendingD
    by fastforce
  show "enc_sections_inv st data inst addr sec src_seg (length tgt_bytes)
           data_bytes inst_bytes addr_bytes tgt_bytes c_out"
    using encode_window_c_loop_invD(13)[OF base] flushed_eq by simp
  show "enc_cache_abs st c_out"
    by (rule encode_window_c_loop_cache_invD(2)[OF inv])
  show "enc_cache_wf c_out"
    by (rule encode_window_c_loop_cache_invD(3)[OF inv])
qed

end

end
