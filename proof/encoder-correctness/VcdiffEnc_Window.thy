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
