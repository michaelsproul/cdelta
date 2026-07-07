(*
  The checked encoder entrypoint.

  vcdiff_encode now performs an explicit upfront arithmetic check
  (vcdiff_enc.c) rejecting any input/capacity configuration outside the
  envelope proven sufficient by Encoder_Bounds. This theory ties the
  runtime behavior to that envelope:

    - `encoder_arith_ok` is the word-level check, conjunct-for-conjunct
      the negations of the lifted guard conditions;
    - `encoder_arith_ok_unat_iff` connects it to the pure-nat
      `encoder_bounds_ok` from Encoder_Bounds;
    - `vcdiff_encode'_rejects_arith_fail`: check fails => Result 0,
      state unchanged;
    - `vcdiff_encode'_writes_encode_spec_of_arith`: check passes (plus
      structural buffer hypotheses) => Result n with n > 0 and the exact
      `encode_spec` bytes;
    - `vcdiff_encode'_checked`: with ONLY structural hypotheses, the
      encoder returns Result 0 or a provably-correct nonzero result —
      a successful encode is always covered by the correctness theorems.
*)
theory VcdiffEnc_Checked
  imports
    VcdiffEnc_Serialize
    CdeltaEncoderBounds.Encoder_Bounds
begin

context vcdiff_enc_global_addresses begin

(* ---------- The word-level check ---------- *)

(* Conjuncts are literally the negated lifted guard conditions of
   vcdiff_encode', in guard order. *)
definition encoder_arith_ok ::
  "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   32 word \<Rightarrow> bool" where
  "encoder_arith_ok out_cap src_len tgt_len pending_cap
      data_cap inst_cap addr_cap \<longleftrightarrow>
     \<not> (0x7FFFFFE0 :: 32 word) \<le> tgt_len \<and>
     \<not> (0xFFFFFFFF :: 32 word) \<le> src_len \<and>
     \<not> 0xFFFFFFFF - tgt_len < src_len \<and>
     \<not> pending_cap < tgt_len \<and>
     \<not> data_cap < tgt_len + 64 \<and>
     \<not> inst_cap < tgt_len + 64 \<and>
     \<not> addr_cap < tgt_len + tgt_len div 4 + 64 \<and>
     \<not> out_cap < 2 * tgt_len + 38"

lemma encoder_arith_okD_words:
  assumes "encoder_arith_ok out_cap src_len tgt_len pending_cap
             data_cap inst_cap addr_cap"
  shows "\<not> (0x7FFFFFE0 :: 32 word) \<le> tgt_len"
    and "\<not> 0xFFFFFFFF - tgt_len < src_len"
    and "\<not> data_cap < tgt_len + 64"
    and "\<not> inst_cap < tgt_len + 64"
    and "\<not> addr_cap < tgt_len + tgt_len div 4 + 64"
    and "\<not> out_cap < 2 * tgt_len + 38"
  using assms by (simp_all add: encoder_arith_ok_def)

(* The word/nat bridge: the C check computes exactly the pure envelope. *)
lemma encoder_arith_ok_unat_iff:
  "encoder_arith_ok out_cap src_len tgt_len pending_cap data_cap inst_cap
     addr_cap \<longleftrightarrow>
   encoder_bounds_ok (unat out_cap) (unat src_len) (unat tgt_len)
     (unat pending_cap) (unat data_cap) (unat inst_cap) (unat addr_cap)"
proof -
  have tgt_iff: "(\<not> (0x7FFFFFE0 :: 32 word) \<le> tgt_len)
                   \<longleftrightarrow> unat tgt_len < 2 ^ 31 - 32"
    by (simp add: word_le_nat_alt not_le)
  have src_iff: "(\<not> (0xFFFFFFFF :: 32 word) \<le> src_len)
                   \<longleftrightarrow> unat src_len < 2 ^ 32 - 1"
    by (simp add: word_le_nat_alt not_le)
  have pend_iff: "(\<not> pending_cap < tgt_len)
                    \<longleftrightarrow> unat tgt_len \<le> unat pending_cap"
    by (simp add: word_less_nat_alt not_less)
  have tgt_lt_2p32: "unat tgt_len < 4294967296"
    using unat_lt2p[of tgt_len] by simp
  have tgt_le_max: "tgt_len \<le> (0xFFFFFFFF :: 32 word)"
  proof -
    have "unat tgt_len \<le> 4294967295" using tgt_lt_2p32 by linarith
    then show ?thesis by (simp add: word_le_nat_alt)
  qed
  have sub_ff: "unat ((0xFFFFFFFF :: 32 word) - tgt_len)
                  = 4294967295 - unat tgt_len"
    using tgt_le_max by (simp add: unat_sub)
  have sum_iff: "(\<not> (0xFFFFFFFF :: 32 word) - tgt_len < src_len)
                   \<longleftrightarrow> unat src_len + unat tgt_len < 2 ^ 32"
  proof -
    have "unat tgt_len \<le> 4294967295" using tgt_lt_2p32 by linarith
    then have "(\<not> unat ((0xFFFFFFFF :: 32 word) - tgt_len) < unat src_len)
                 \<longleftrightarrow> unat src_len + unat tgt_len < 4294967296"
      by (simp add: sub_ff) linarith
    then show ?thesis
      by (simp add: word_less_nat_alt)
  qed
  show ?thesis
  proof (cases "unat tgt_len < 2 ^ 31 - 32")
    case False
    then show ?thesis
      using tgt_iff
      by (auto simp: encoder_arith_ok_def encoder_bounds_ok_def)
  next
    case True
    have t_bd: "unat tgt_len < 2147483616" using True by simp
    have no_ovf: "\<And>a b :: 32 word. unat a + unat b < 4294967296 \<Longrightarrow>
                    unat (a + b) = unat a + unat b"
      using unat_add_lem by force
    have plus64: "unat (tgt_len + 64) = unat tgt_len + 64"
      using no_ovf[of tgt_len "64 :: 32 word"] t_bd by simp
    have div4: "unat (tgt_len div 4) = unat tgt_len div 4"
      by (simp add: unat_div)
    have div4_le: "unat tgt_len div 4 \<le> unat tgt_len"
      by (rule div_le_dividend)
    have inner: "unat (tgt_len + tgt_len div 4)
                   = unat tgt_len + unat tgt_len div 4"
      using no_ovf[of tgt_len "tgt_len div 4"] div4 div4_le t_bd by simp
    have addr_sum: "unat (tgt_len + tgt_len div 4 + 64)
                      = unat tgt_len + unat tgt_len div 4 + 64"
      using no_ovf[of "tgt_len + tgt_len div 4" "64 :: 32 word"] inner div4_le
            t_bd
      by simp
    have two_t: "unat (2 * tgt_len) = 2 * unat tgt_len"
    proof -
      have "unat (2 :: 32 word) * unat tgt_len < 4294967296"
        using t_bd by simp
      then show ?thesis
        using unat_mult_lem[of "2 :: 32 word" tgt_len] by simp
    qed
    have out_sum: "unat (2 * tgt_len + 38) = 2 * unat tgt_len + 38"
      using no_ovf[of "2 * tgt_len" "38 :: 32 word"] two_t t_bd by simp
    have data_iff: "(\<not> data_cap < tgt_len + 64)
                      \<longleftrightarrow> unat tgt_len + 64 \<le> unat data_cap"
      by (simp add: word_less_nat_alt not_less plus64)
    have inst_iff: "(\<not> inst_cap < tgt_len + 64)
                      \<longleftrightarrow> unat tgt_len + 64 \<le> unat inst_cap"
      by (simp add: word_less_nat_alt not_less plus64)
    have addr_iff: "(\<not> addr_cap < tgt_len + tgt_len div 4 + 64)
                      \<longleftrightarrow> unat tgt_len + unat tgt_len div 4 + 64
                            \<le> unat addr_cap"
      by (simp add: word_less_nat_alt not_less addr_sum)
    have out_iff: "(\<not> out_cap < 2 * tgt_len + 38)
                     \<longleftrightarrow> 2 * unat tgt_len + 38 \<le> unat out_cap"
      by (simp add: word_less_nat_alt not_less out_sum)
    show ?thesis
      unfolding encoder_arith_ok_def encoder_bounds_ok_def
      by (simp add: tgt_iff src_iff sum_iff pend_iff data_iff inst_iff
                    addr_iff out_iff)
  qed
qed

(* ---------- Structural (validity/disjointness-only) buffers ---------- *)

(* encoder_buffers_ok minus its four arithmetic conjuncts; those are
   now enforced at runtime by the entrypoint check. *)
definition encoder_buffers_valid ::
  "lifted_globals \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   32 word ptr \<Rightarrow> 32 word ptr \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> bool" where
  "encoder_buffers_valid s out out_cap src src_len tgt tgt_len head_arr next_arr
      pending pending_cap data data_cap inst inst_cap addr addr_cap \<longleftrightarrow>
     buf_valid s out (unat out_cap) \<and>
     buf_valid s src (unat src_len) \<and>
     buf_valid s tgt (unat tgt_len) \<and>
     buf_valid s pending (unat pending_cap) \<and>
     buf_valid s data (unat data_cap) \<and>
     buf_valid s inst (unat inst_cap) \<and>
     buf_valid s addr (unat addr_cap) \<and>
     ptr_range_distinct out (unat out_cap) \<and>
     ptr_range_distinct src (unat src_len) \<and>
     ptr_range_distinct tgt (unat tgt_len) \<and>
     ptr_range_distinct pending (unat pending_cap) \<and>
     ptr_range_distinct data (unat data_cap) \<and>
     ptr_range_distinct inst (unat inst_cap) \<and>
     ptr_range_distinct addr (unat addr_cap) \<and>
     bufs_disjoint out (unat out_cap) src (unat src_len) \<and>
     bufs_disjoint out (unat out_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint out (unat out_cap) pending (unat pending_cap) \<and>
     bufs_disjoint out (unat out_cap) data (unat data_cap) \<and>
     bufs_disjoint out (unat out_cap) inst (unat inst_cap) \<and>
     bufs_disjoint out (unat out_cap) addr (unat addr_cap) \<and>
     bufs_disjoint pending (unat pending_cap) src (unat src_len) \<and>
     bufs_disjoint pending (unat pending_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint pending (unat pending_cap) data (unat data_cap) \<and>
     bufs_disjoint pending (unat pending_cap) inst (unat inst_cap) \<and>
     bufs_disjoint pending (unat pending_cap) addr (unat addr_cap) \<and>
     bufs_disjoint data (unat data_cap) src (unat src_len) \<and>
     bufs_disjoint data (unat data_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint data (unat data_cap) inst (unat inst_cap) \<and>
     bufs_disjoint data (unat data_cap) addr (unat addr_cap) \<and>
     bufs_disjoint inst (unat inst_cap) src (unat src_len) \<and>
     bufs_disjoint inst (unat inst_cap) tgt (unat tgt_len) \<and>
     bufs_disjoint inst (unat inst_cap) addr (unat addr_cap) \<and>
     bufs_disjoint addr (unat addr_cap) src (unat src_len) \<and>
     bufs_disjoint addr (unat addr_cap) tgt (unat tgt_len)"

lemma encoder_buffers_ok_of_valid_arith:
  assumes valid:
        "encoder_buffers_valid s out out_cap src src_len tgt tgt_len head_arr
           next_arr pending pending_cap data data_cap inst inst_cap addr
           addr_cap"
      and pend: "unat tgt_len \<le> unat pending_cap"
      and dcap: "unat tgt_len + 64 \<le> unat data_cap"
      and icap: "unat tgt_len + 64 \<le> unat inst_cap"
      and acap: "unat tgt_len + 64 \<le> unat addr_cap"
  shows "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr
           next_arr pending pending_cap data data_cap inst inst_cap addr
           addr_cap"
  using assms
  by (simp add: encoder_buffers_valid_def encoder_buffers_ok_def)

(* ---------- Reject: check fails => Result 0, state unchanged ---------- *)

lemma vcdiff_encode'_rejects_arith_fail:
  assumes bad: "\<not> encoder_arith_ok out_cap src_len tgt_len pending_cap
                    data_cap inst_cap addr_cap"
  shows "vcdiff_encode' out out_cap src src_len tgt tgt_len head_arr next_arr
           pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
         \<lbrace> \<lambda>r t. r = Result (0 :: 32 word) \<and> t = s \<rbrace>"
  unfolding vcdiff_encode'_def
  apply runs_to_vcg
  using bad by (auto simp: encoder_arith_ok_def)

(* ---------- Discharge the final-section caps from the envelope ---------- *)

lemma encoder_final_section_caps_ok_of_arith:
  assumes src_bound: "length src_bytes < 2 ^ 32"
      and data_cap_ok: "length tgt_bytes \<le> unat data_cap"
      and inst_cap_ok: "length tgt_bytes \<le> unat inst_cap"
      and addr_cap_ok: "5 * length tgt_bytes \<le> 4 * unat addr_cap"
  shows "encoder_final_section_caps_ok src_bytes tgt_bytes
           data_cap inst_cap addr_cap"
proof -
  define fin where
    "fin = encode_window_full_loop (length tgt_bytes + 1) src_bytes tgt_bytes
             (build_index_spec src_bytes) enc_full_init"
  note b = encode_window_final_state_section_bounds
             [OF src_bound, of tgt_bytes, folded fin_def]
  have d: "length (enc_data fin) \<le> unat data_cap"
    using b(1) data_cap_ok by linarith
  have i: "length (enc_inst fin) \<le> unat inst_cap"
    using b(2) inst_cap_ok by linarith
  have a: "length (enc_addr fin) \<le> unat addr_cap"
    using b(3) addr_cap_ok by linarith
  show ?thesis
    using d i a
    by (simp add: encoder_final_section_caps_ok_def
                  encode_window_final_spec_state_def fin_def)
qed

(* ---------- Success under the envelope ---------- *)

theorem vcdiff_encode'_writes_encode_spec_of_arith:
  fixes out src tgt pending data inst addr :: "8 word ptr"
    and out_cap src_len tgt_len pending_cap data_cap inst_cap addr_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
        "encoder_input_rel s src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_valid s out out_cap src src_len tgt tgt_len head_arr
           next_arr pending pending_cap data data_cap inst inst_cap addr
           addr_cap"
      and arith:
        "encoder_arith_ok out_cap src_len tgt_len pending_cap data_cap
           inst_cap addr_cap"
      and head_valid:
        "\<And>h. h < hash_size \<Longrightarrow>
          ptr_valid (heap_typing s) (head_arr +\<^sub>p int h)"
      and next_valid:
        "\<And>p. p < unat src_len \<Longrightarrow>
          ptr_valid (heap_typing s) (next_arr +\<^sub>p int p)"
      and head_no_alias:
        "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
          head_arr +\<^sub>p int h \<noteq> head_arr +\<^sub>p int bucket"
      and next_no_alias:
        "\<And>q p. \<lbrakk>q < unat src_len; p < unat src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      and next_head_disjoint:
        "\<And>h p. \<lbrakk>h < hash_size; p < unat src_len\<rbrakk> \<Longrightarrow>
          head_arr +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
      and head_next_disjoint:
        "\<And>q bucket. \<lbrakk>q < unat src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> head_arr +\<^sub>p int bucket"
  shows "vcdiff_encode' out out_cap src src_len tgt tgt_len head_arr next_arr
            pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>n.
               r = Result n \<and> 0 < unat n \<and>
               encoder_success_post out src_bytes tgt_bytes n s t \<rbrace>"
proof -
  note B = arith[unfolded encoder_arith_ok_unat_iff]
  have src_len_eq: "unat src_len = length src_bytes"
    and tgt_len_eq: "unat tgt_len = length tgt_bytes"
    using input by (simp_all add: encoder_input_rel_def)
  have src_bound: "length src_bytes < 2 ^ 32"
    using src_len_eq unat_lt2p[of src_len] by simp
  have tgt_small_nat: "length tgt_bytes < 2 ^ 31 - 32"
    using B tgt_len_eq by (simp add: encoder_bounds_ok_def)
  have src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
    using B src_len_eq tgt_len_eq by (simp add: encoder_bounds_ok_def)
  have pending_cap_ok: "unat tgt_len \<le> unat pending_cap"
    using B by (simp add: encoder_bounds_ok_def)
  have src_len_word: "unat src_len < unat (no_entry32 :: 32 word)"
    using B by (simp add: encoder_bounds_ok_def)
  note arith_caps = encoder_bounds_ok_addr_arith[OF B]
  have dcap: "unat tgt_len + 64 \<le> unat data_cap"
    and icap: "unat tgt_len + 64 \<le> unat inst_cap"
    using B by (simp_all add: encoder_bounds_ok_def)
  have acap: "unat tgt_len + 64 \<le> unat addr_cap"
    using arith_caps(2) by simp
  have buffers_ok:
    "encoder_buffers_ok s out out_cap src src_len tgt tgt_len head_arr
       next_arr pending pending_cap data data_cap inst inst_cap addr addr_cap"
    by (rule encoder_buffers_ok_of_valid_arith
         [OF buffers pending_cap_ok dcap icap acap])
  have final_caps:
    "encoder_final_section_caps_ok src_bytes tgt_bytes
       data_cap inst_cap addr_cap"
  proof (rule encoder_final_section_caps_ok_of_arith[OF src_bound])
    show "length tgt_bytes \<le> unat data_cap"
      using dcap tgt_len_eq by linarith
    show "length tgt_bytes \<le> unat inst_cap"
      using icap tgt_len_eq by linarith
    show "5 * length tgt_bytes \<le> 4 * unat addr_cap"
      using arith_caps(1) tgt_len_eq by simp
  qed
  have fit:
    "sections_fit_32 src_bytes tgt_bytes
       (encode_window_full_spec src_bytes tgt_bytes)"
    by (rule encode_window_full_spec_fits_32[OF src_bound tgt_small_nat])
  have out_cap_ok:
    "length (encode_spec src_bytes tgt_bytes) \<le> unat out_cap"
    by (rule encoder_bounds_ok_out_cap)
       (use B src_len_eq tgt_len_eq in simp)
  have encoded_len_word:
    "length (encode_spec src_bytes tgt_bytes) < 2 ^ 32"
    by (rule encode_spec_length_lt_2p32[OF src_bound tgt_small_nat])
  note W = encoder_arith_okD_words[OF arith]
  have base:
    "vcdiff_encode' out out_cap src src_len tgt tgt_len head_arr next_arr
       pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
     \<lbrace> \<lambda>r t. \<exists>n.
         r = Result n \<and>
         encoder_success_post out src_bytes tgt_bytes n s t \<rbrace>"
    by (rule vcdiff_encode'_writes_encode_spec_topdown[
        OF input buffers_ok final_caps pending_cap_ok src_len_word
           W(1) W(2) W(3) W(4) W(5) W(6)
           head_valid next_valid head_no_alias next_no_alias
           next_head_disjoint head_next_disjoint
           fit src_tgt_bound out_cap_ok encoded_len_word])
  show ?thesis
    apply (rule runs_to_weaken[OF base])
    using encode_spec_length_pos[of src_bytes tgt_bytes]
    by (auto simp: encoder_success_post_def)
qed

(* ---------- The headline: structural hypotheses only ---------- *)

theorem vcdiff_encode'_checked:
  fixes out src tgt pending data inst addr :: "8 word ptr"
    and out_cap src_len tgt_len pending_cap data_cap inst_cap addr_cap :: "32 word"
    and head_arr next_arr :: "32 word ptr"
  assumes input:
        "encoder_input_rel s src src_len tgt tgt_len src_bytes tgt_bytes"
      and buffers:
        "encoder_buffers_valid s out out_cap src src_len tgt tgt_len head_arr
           next_arr pending pending_cap data data_cap inst inst_cap addr
           addr_cap"
      and head_valid:
        "\<And>h. h < hash_size \<Longrightarrow>
          ptr_valid (heap_typing s) (head_arr +\<^sub>p int h)"
      and next_valid:
        "\<And>p. p < unat src_len \<Longrightarrow>
          ptr_valid (heap_typing s) (next_arr +\<^sub>p int p)"
      and head_no_alias:
        "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
          head_arr +\<^sub>p int h \<noteq> head_arr +\<^sub>p int bucket"
      and next_no_alias:
        "\<And>q p. \<lbrakk>q < unat src_len; p < unat src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> next_arr +\<^sub>p int p"
      and next_head_disjoint:
        "\<And>h p. \<lbrakk>h < hash_size; p < unat src_len\<rbrakk> \<Longrightarrow>
          head_arr +\<^sub>p int h \<noteq> next_arr +\<^sub>p int p"
      and head_next_disjoint:
        "\<And>q bucket. \<lbrakk>q < unat src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
          next_arr +\<^sub>p int q \<noteq> head_arr +\<^sub>p int bucket"
  shows "vcdiff_encode' out out_cap src src_len tgt tgt_len head_arr next_arr
            pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>n.
               r = Result n \<and>
               (n = 0 \<or>
                (0 < unat n \<and>
                 encoder_arith_ok out_cap src_len tgt_len pending_cap
                   data_cap inst_cap addr_cap \<and>
                 encoder_success_post out src_bytes tgt_bytes n s t)) \<rbrace>"
proof (cases "encoder_arith_ok out_cap src_len tgt_len pending_cap data_cap
                inst_cap addr_cap")
  case False
  show ?thesis
    by (rule runs_to_weaken[OF vcdiff_encode'_rejects_arith_fail[OF False]])
       auto
next
  case True
  show ?thesis
    by (rule runs_to_weaken[OF vcdiff_encode'_writes_encode_spec_of_arith[
          OF input buffers True head_valid next_valid head_no_alias
             next_no_alias next_head_disjoint head_next_disjoint]])
       (use True in auto)
qed

end

end
