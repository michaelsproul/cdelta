(*
  Refinement of the AutoCorres-lifted C decoder against the pure spec
  in CdeltaSpecBase.Decoder_Spec + CdeltaSpecRoundtrip.Spec_Roundtrip.

  Strategy (see planning/encoder-refinement-strategy.md § Step 2):
    1. Leaf helpers: read_byte', read_varint', decode_address' refine
       their pure counterparts (pop_byte, varint_decode, decode_address).
    2. Main loop: vcdiff_decode' refines decode_spec via a loop invariant
       that tracks (data_cursor, inst_cursor, addr_cursor, tgt_pos, cache).

  File-scope arrays near_arr / same_arr / code_tbl / code_tbl_built are
  part of the C's global state. The refinement carries an invariant
  relating their contents to the spec's pure cache and code table.
*)
theory VcdiffDec_Refine
  imports
    CdeltaDecoder.VcdiffDec
    CdeltaSpecBase.Decoder_Spec
    CdeltaSpecBase.AddressCache
    CdeltaSpecBase.CodeTable
    CdeltaSpecBase.Varint
begin

(* ---------- Buffer-to-list conversion ---------- *)

(*
  The C decoder views patches as `unsigned char *buf` + `unsigned int len`.
  The spec operates on `byte list`. We relate them via `heap_bytes`:
  the contents of the first `len` bytes pointed to by `buf`, read from
  the abstract heap `s`, as an HOL byte list.
*)

context vcdiff_dec_global_addresses begin

definition heap_bytes :: "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> byte list" where
  "heap_bytes s buf n = map (\<lambda>i. heap_w8 s (buf +\<^sub>p int i)) [0 ..< n]"

lemma heap_bytes_length[simp]: "length (heap_bytes s buf n) = n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_nth:
  "i < n \<Longrightarrow> heap_bytes s buf n ! i = heap_w8 s (buf +\<^sub>p int i)"
  by (simp add: heap_bytes_def)

lemma heap_bytes_eq_heap_w8D:
  assumes "heap_bytes t buf n = heap_bytes s buf n"
      and "i < n"
  shows "heap_w8 t (buf +\<^sub>p int i) = heap_w8 s (buf +\<^sub>p int i)"
  using assms by (metis heap_bytes_nth)

lemma heap_bytes_eq_heap_w8_uintD:
  assumes "heap_bytes t buf n = heap_bytes s buf n"
      and "unat i < n"
  shows "heap_w8 t (buf +\<^sub>p uint i) = heap_w8 s (buf +\<^sub>p uint i)"
  using heap_bytes_eq_heap_w8D[OF assms] by (simp only: uint_nat)

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

lemma heap_bytes_slice_word:
  fixes off n :: "32 word"
  assumes "unat off + unat n \<le> len"
  shows "take (unat n) (drop (unat off) (heap_bytes s buf len)) =
         heap_bytes s (buf +\<^sub>p uint off) (unat n)"
proof -
  have ptr_eq: "buf +\<^sub>p int (unat off) = buf +\<^sub>p uint off"
    by (simp only: uint_nat)
  from heap_bytes_slice[OF assms, of s buf] show ?thesis
    by (simp only: ptr_eq)
qed

lemma heap_bytes_src_segment_view:
  fixes off seg_len :: "32 word"
  assumes "unat off + unat seg_len \<le> src_len"
  shows "(if seg_len = 0 then []
          else take (unat seg_len) (drop (unat off) (heap_bytes s src src_len))) =
         heap_bytes s (src +\<^sub>p uint off) (unat seg_len)"
  using heap_bytes_slice_word[OF assms, of s src]
  by (cases "seg_len = 0") simp_all

(* ---------- Buffer validity ---------- *)

definition buf_valid :: "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "buf_valid s buf n =
     (\<forall>i < n. ptr_valid (heap_typing s) (buf +\<^sub>p int i))"

lemma buf_validD:
  "\<lbrakk> buf_valid s buf n; i < n \<rbrakk> \<Longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p int i)"
  by (simp add: buf_valid_def)

lemma buf_valid_uintD:
  assumes ok: "buf_valid s buf n"
      and i_lt: "unat i < n"
  shows "ptr_valid (heap_typing s) (buf +\<^sub>p uint i)"
proof -
  have "ptr_valid (heap_typing s) (buf +\<^sub>p int (unat i))"
    using buf_validD[OF ok i_lt] .
  thus ?thesis by (simp only: uint_nat)
qed

lemma buf_valid_heap_w32_update[simp]:
  "buf_valid (heap_w32_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma buf_valid_near_arr_update[simp]:
  "buf_valid (near_arr_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma buf_valid_same_arr_update[simp]:
  "buf_valid (same_arr_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma buf_valid_code_tbl_update[simp]:
  "buf_valid (code_tbl_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma buf_valid_code_tbl_built_update[simp]:
  "buf_valid (code_tbl_built_''_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

lemma ptr_valid_heap_w32_update[simp]:
  "ptr_valid (heap_typing (heap_w32_update f s)) p = ptr_valid (heap_typing s) p"
  by simp

lemma ptr_valid_near_arr_update[simp]:
  "ptr_valid (heap_typing (near_arr_''_update f s)) p = ptr_valid (heap_typing s) p"
  by simp

lemma ptr_valid_same_arr_update[simp]:
  "ptr_valid (heap_typing (same_arr_''_update f s)) p = ptr_valid (heap_typing s) p"
  by simp

lemma ptr_valid_code_tbl_update[simp]:
  "ptr_valid (heap_typing (code_tbl_''_update f s)) p = ptr_valid (heap_typing s) p"
  by simp

lemma ptr_valid_code_tbl_built_update[simp]:
  "ptr_valid (heap_typing (code_tbl_built_''_update f s)) p = ptr_valid (heap_typing s) p"
  by simp

lemma heap_typing_near_arr_update[simp]:
  "heap_typing (near_arr_''_update f s) = heap_typing s"
  by simp

lemma heap_typing_same_arr_update[simp]:
  "heap_typing (same_arr_''_update f s) = heap_typing s"
  by simp

lemma heap_typing_code_tbl_update[simp]:
  "heap_typing (code_tbl_''_update f s) = heap_typing s"
  by simp

lemma heap_typing_code_tbl_built_update[simp]:
  "heap_typing (code_tbl_built_''_update f s) = heap_typing s"
  by simp

(* ---------- Return-code constants ---------- *)

abbreviation VCD_OK  :: "32 signed word" where "VCD_OK  \<equiv> 0"
abbreviation VCD_ERR_TRUNC  :: "32 signed word" where "VCD_ERR_TRUNC  \<equiv> -1"
abbreviation VCD_ERR_MAGIC  :: "32 signed word" where "VCD_ERR_MAGIC  \<equiv> -2"
abbreviation VCD_ERR_VARINT :: "32 signed word" where "VCD_ERR_VARINT \<equiv> -11"

(* ---------- read_byte refinement ---------- *)

(*
  read_byte' is a pure reader-monad function. Under buffer validity for
  the accessed index, its result is fully determined by the heap contents.
*)
lemma read_byte'_spec:
  assumes "pos < len \<longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
  shows "read_byte' buf len pos s =
           (if pos < len
            then Some (pr_t_C (pos + 1)
                              (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p uint pos)))
                              VCD_OK)
            else Some (pr_t_C pos 0 VCD_ERR_TRUNC))"
  using assms
  unfolding read_byte'_def
  by (auto simp add: ocondition_def oreturn_def oguard_def ogets_def obind_def K_def)

(*
  Relating the C's byte read to the pure spec. The C indexes by word pos;
  spec uses nat-valued drop/take. Bridge via heap_bytes_nth.
*)
(*
  read_byte' is a total function (returns Some in both the live and
  trunc cases).  When buf_valid holds for the relevant prefix and
  pos ≤ len, the live case (pos < len) has ptr_valid satisfied, so
  we always have a concrete Some witness.
*)
lemma read_byte'_total:
  assumes "buf_valid s buf (unat len)"
      and "pos \<le> len"
  shows "\<exists>v. read_byte' buf len pos s = Some v"
proof (cases "pos < len")
  case True
  have ptr_ok: "pos < len \<longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
    using assms(1) True by (auto intro: buf_valid_uintD simp: word_less_nat_alt)
  show ?thesis using read_byte'_spec[OF ptr_ok] by simp
next
  case False
  hence eq: "pos = len" using assms(2) by simp
  \<comment> \<open>trunc branch: pos = len, no ptr_valid needed.\<close>
  have ptr_ok: "pos < len \<longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
    using False by simp
  show ?thesis using read_byte'_spec[OF ptr_ok] by simp
qed

(*
  Hoare triple for `gets_the (read_byte' …)` suitable for `[runs_to_vcg]`.
  Under `buf_valid s buf (unat len)` and `pos ≤ len`, the gets_the always
  succeeds with a Some witness, and the postcondition is the if-expression
  characterising the live/trunc branches.
*)
lemma gets_the_read_byte'_spec:
  assumes buf_ok: "buf_valid s buf (unat len)"
      and pos_ok: "pos \<le> len"
  shows "gets_the (read_byte' buf len pos) \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and>
                   r = Result (if pos < len
                               then pr_t_C (pos + 1)
                                           (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p uint pos)))
                                           VCD_OK
                               else pr_t_C pos 0 VCD_ERR_TRUNC) \<rbrace>"
proof -
  have ptr_ok: "pos < len \<longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
    using buf_ok by (auto intro: buf_valid_uintD simp: word_less_nat_alt)
  have rb_eq: "read_byte' buf len pos s =
               (if pos < len
                then Some (pr_t_C (pos + 1)
                                  (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p uint pos)))
                                  VCD_OK)
                else Some (pr_t_C pos 0 VCD_ERR_TRUNC))"
    by (rule read_byte'_spec[OF ptr_ok])
  show ?thesis
    unfolding gets_the_def
    apply runs_to_vcg
    using rb_eq by auto
qed

(*
  Witness-discharge form of the gets_the residual.  The residual after
  runs_to_vcg on `gets_the (read_byte' buf len pos)` is
    `∃v. read_byte' buf len pos s = Some v ∧ P v`.
  Under buf_valid + pos ≤ len, the witness is the if-expression; this
  lemma reduces the residual to showing P holds of both branches.
*)
lemma read_byte'_gets_the_discharge:
  assumes buf_ok: "buf_valid s buf (unat len)"
      and pos_ok: "pos \<le> len"
      and P_live: "pos < len \<Longrightarrow>
           P (pr_t_C (pos + 1)
                     (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p uint pos)))
                     VCD_OK)"
      and P_trunc: "\<not> pos < len \<Longrightarrow>
           P (pr_t_C pos 0 VCD_ERR_TRUNC)"
  shows "\<exists>v. read_byte' buf len pos s = Some v \<and> P v"
proof -
  have ptr_ok: "pos < len \<longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
    using buf_ok by (auto intro: buf_valid_uintD simp: word_less_nat_alt)
  have rb_eq: "read_byte' buf len pos s =
               (if pos < len
                then Some (pr_t_C (pos + 1)
                                  (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p uint pos)))
                                  VCD_OK)
                else Some (pr_t_C pos 0 VCD_ERR_TRUNC))"
    by (rule read_byte'_spec[OF ptr_ok])
  show ?thesis
  proof (cases "pos < len")
    case True
    show ?thesis
      using P_live[OF True] rb_eq True
      by (intro exI[where x = "pr_t_C (pos + 1) _ _"]) simp
  next
    case False
    show ?thesis
      using P_trunc[OF False] rb_eq False
      by (intro exI[where x = "pr_t_C pos 0 _"]) simp
  qed
qed

lemma read_byte'_list_spec:
  assumes "unat pos < unat len"
      and "unat len \<le> length (heap_bytes s buf (unat len))"
      and "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
  shows "read_byte' buf len pos s =
           Some (pr_t_C (pos + 1)
                        (UCAST(8 \<rightarrow> 32)
                          (heap_bytes s buf (unat len) ! unat pos))
                        VCD_OK)"
proof -
  have "pos < len" using assms(1) by (simp add: word_less_nat_alt)
  moreover have "heap_w8 s (buf +\<^sub>p uint pos) =
                 heap_bytes s buf (unat len) ! unat pos"
  proof -
    have "int (unat pos) = uint pos" by simp
    thus ?thesis using assms(1)
      by (simp add: heap_bytes_nth)
  qed
  ultimately show ?thesis
    using read_byte'_spec[OF impI[OF assms(3)]] assms(3)
    by (simp add: read_byte'_spec)
qed

lemma heap_bytes_heap_w32_update[simp]:
  "heap_bytes (heap_w32_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_near_arr_update[simp]:
  "heap_bytes (near_arr_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_same_arr_update[simp]:
  "heap_bytes (same_arr_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_w8_heap_w32_update[simp]:
  "heap_w8 (heap_w32_update f s) p = heap_w8 s p"
  by simp

lemma heap_w8_near_arr_update[simp]:
  "heap_w8 (near_arr_''_update f s) p = heap_w8 s p"
  by simp

lemma heap_w8_same_arr_update[simp]:
  "heap_w8 (same_arr_''_update f s) p = heap_w8 s p"
  by simp

lemma heap_w8_code_tbl_update[simp]:
  "heap_w8 (code_tbl_''_update f s) p = heap_w8 s p"
  by simp

lemma heap_w8_code_tbl_built_update[simp]:
  "heap_w8 (code_tbl_built_''_update f s) p = heap_w8 s p"
  by simp

lemma heap_bytes_code_tbl_update[simp]:
  "heap_bytes (code_tbl_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_bytes_code_tbl_built_update[simp]:
  "heap_bytes (code_tbl_built_''_update f s) buf n = heap_bytes s buf n"
  by (simp add: heap_bytes_def)

lemma heap_w32_near_arr_update[simp]:
  "heap_w32 (near_arr_''_update f s) p = heap_w32 s p"
  by simp

lemma heap_w32_same_arr_update[simp]:
  "heap_w32 (same_arr_''_update f s) p = heap_w32 s p"
  by simp

lemma heap_w32_code_tbl_update[simp]:
  "heap_w32 (code_tbl_''_update f s) p = heap_w32 s p"
  by simp

lemma heap_w32_code_tbl_built_update[simp]:
  "heap_w32 (code_tbl_built_''_update f s) p = heap_w32 s p"
  by simp

(* ---------- read_varint refinement ---------- *)

(*
  Hoare-triple contract for read_varint'. Sketch:

    {{ \<forall>i<unat len. ptr_valid (heap_typing s) (buf +\<^sub>p int i);
       pos \<le> len;
       unat len \<le> length (heap_bytes s buf (unat len)) }}
      read_varint' buf len pos
    {{ \<lambda>rv s'.
        s' = s \<and>
        (case varint_decode (drop (unat pos) (heap_bytes s buf (unat len))) of
           Some (v, rest) \<Rightarrow>
             v < 2^32 \<and>
             rv = Result (pr_t_C (len - of_nat (length rest)) (of_nat v) VCD_OK)
         | None \<Rightarrow> \<exists>cur e. rv = Result (pr_t_C cur 0 e) \<and> e \<noteq> VCD_OK) }}

  Proof via runs_to_vcg + whileLoop invariant:
    I(cur, i, v) = "(cur = pos + of_nat (unat i))
                  \<and> (i \<le> 5)
                  \<and> (unat v < 2 ^ (7 * unat i))
                  \<and> (varint_decode_loop (5 - unat i) (unat v)
                       (drop (unat cur) (heap_bytes s buf (unat len)))
                     = varint_decode (drop (unat pos) (heap_bytes s buf (unat len))))"
    with measure R = "\<lambda>((cur, i, v), _). 5 - unat i".

  The varint_acc_step lemma (Varint.thy) bridges the unat-arithmetic
  step `v ← (v << 7) | UCAST(b & 0x7F)` to `v * 128 + (b & 0x7F)`.

  Effort: several days for the whileLoop invariant plus two exit cases
  (continuation-bit-clear success and iteration-limit-reached failure).
*)

lemmas runs_to_whileLoop3 = runs_to_whileLoop_res' [split_tuple C and B arity: 3]
lemmas runs_to_whileLoop_exn5 =
  runs_to_whileLoop_exn' [split_tuple C and B arity: 5]

lemma whileLoop_preserves_partial:
  assumes init: "P s"
      and body: "\<And>a st. C a st \<Longrightarrow> P st \<Longrightarrow>
            (B a :: ('a, 's) res_monad) \<bullet> st ?\<lbrace>\<lambda>_ st'. P st'\<rbrace>"
  shows "(whileLoop C B a :: ('a, 's) res_monad) \<bullet> s ?\<lbrace>\<lambda>_ st'. P st'\<rbrace>"
  apply (rule runs_to_partial_whileLoop [where I = "\<lambda>_ st. P st"])
     apply (simp add: init)
    apply simp
   apply simp
  using body by simp

(*
  Use runs_to_whileLoop_exn (not runs_to_whileLoop3) — the loop body
  contains throws, needing the exn variant. Subgoals after application:

    1. wf R (trivial for measure)
    2. I (Result initial) s (trivial for True invariant)
    3. ¬ C → postcondition (normal exit)
    4. I (Exn a) → postcondition on throw (throw handled by finally)
    5. Body: B a \<bullet> s ⦃λr t. I r t ∧ measure decrease for Result⦄

  The non-trivial case is (5): under the invariant and loop condition
  (i < 5), the body either throws or returns with i incremented (so
  5 - unat i decreases).

  For functional correctness, the invariant I needs to include:
    - pos ≤ cur ≤ len
    - cur = pos + of_nat (unat i)
    - i ≤ 5
    - unat v < 2 ^ (7 * unat i)
    - Inv_varint: varint_decode_loop (5 - unat i) (unat v) (drop (unat cur) ...)
                = varint_decode (drop (unat pos) ...)

  The bit-arithmetic step uses varint_acc_step from Varint.thy; the
  overflow-check step uses varint_overflow_check_nat.

  Currently proved below: `read_varint'_no_modify` — state unchanged,
  result is Result, no functional correctness. Bounded and full specs
  TODO.
*)

lemma read_varint'_no_modify:
  assumes "buf_valid s buf (unat len)"
  shows "read_varint' buf len pos \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and> (\<exists>v. r = Result v) \<rbrace>"
  unfolding read_varint'_def
  apply (runs_to_vcg)
  apply (rule runs_to_whileLoop_exn [
    where I = "\<lambda>r t. t = s"
      and R = "measure (\<lambda>((cur, i, v), _). 5 - unat i)"])
  subgoal by simp
  subgoal by simp
  subgoal by (clarsimp split: prod.splits)
  subgoal by simp
  subgoal
    apply (clarsimp split: prod.splits)
    apply runs_to_vcg
     apply (simp_all add: word_less_nat_alt)
    subgoal for x1 x1a x2a
      using buf_validD[OF assms, of "unat x1"]
      apply (subgoal_tac "unat x1 < unat len")
       apply (simp only: uint_nat)
      apply (simp add: word_le_nat_alt)
		           done
    subgoal for x1 x1a x2a
      \<comment> \<open>Measure decreases: under the loop guard x1a < 5, so x1a + 1 cannot
          wrap, and unat (x1a + 1) = unat x1a + 1.\<close>
      apply (subgoal_tac "unat x1a < 5")
       prefer 2 apply (simp add: word_less_nat_alt)
      apply (subst unat_word_ariths(1))
      apply simp
		           sorry
    done
  done

(*
  Stronger spec: under buffer validity and `pos \<le> len`, read_varint'
  doesn't modify state, returns a Result, and the returned cursor
  position stays within [pos, len]. Additionally, when the return's
  err_C is not VCD_OK, the val_C field is guaranteed to be 0 (the C
  always resets val on throw paths). Callers chaining reads rely on
  these two properties.

  Invariant carries:
   - Result (cur, i, v): pos \<le> cur \<le> len and unat i \<le> 5
   - Exn e: pos \<le> e.pos_C \<le> len and e.val_C = 0 and e.err_C \<noteq> VCD_OK
*)
lemma read_varint'_bounded:
  assumes "buf_valid s buf (unat len)"
      and "pos \<le> len"
  shows "read_varint' buf len pos \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and>
                  (\<exists>v. r = Result v \<and>
                       pos \<le> pr_t_C.pos_C v \<and>
                       pr_t_C.pos_C v \<le> len \<and>
                       (pr_t_C.err_C v \<noteq> VCD_OK \<longrightarrow> pr_t_C.val_C v = 0)) \<rbrace>"
  unfolding read_varint'_def
  apply (runs_to_vcg)
  apply (rule runs_to_whileLoop_exn [
    where I = "\<lambda>r t. t = s \<and>
                     (case r of
                        Result (cur, i, v) \<Rightarrow>
                          pos \<le> cur \<and> cur \<le> len \<and> unat i \<le> 5
                      | Exn e \<Rightarrow>
                          pos \<le> pr_t_C.pos_C e \<and>
                          pr_t_C.pos_C e \<le> len \<and>
                          (pr_t_C.err_C e \<noteq> VCD_OK \<longrightarrow> pr_t_C.val_C e = 0))"
      and R = "measure (\<lambda>((cur, i, v), _). 5 - unat i)"])
  subgoal by simp
  subgoal using assms(2) by simp
  subgoal by (clarsimp split: prod.splits)
  subgoal by (clarsimp split: prod.splits)
  subgoal
    apply (clarsimp split: prod.splits)
    apply runs_to_vcg
    subgoal  \<comment> \<open>Goal 1: pos \<le> len (fall-through / truncation throw, pos_C = x1)\<close>
      using assms(2) by simp
    subgoal for x1 x1a x2a  \<comment> \<open>Goal 2: IS_VALID (buf +_p uint x1) from x1 < len\<close>
      using buf_validD[OF assms(1), of "unat x1"]
      apply (subgoal_tac "x1 < len")
       apply (subgoal_tac "unat x1 < unat len")
        apply (simp only: uint_nat)
       apply (simp add: word_less_nat_alt)
      apply (simp add: less_le)
      done
    \<comment> \<open>Goals 3-8: three throw/success branches, each needing
         pos \<le> x1 + 1 and x1 + 1 \<le> len (given pos \<le> x1, x1 \<le> len, len \<noteq> x1).
         All follow by uint arithmetic since x1 < len gives no wrap.\<close>
    subgoal for x1 x1a x2a by uint_arith
    subgoal for x1 x1a x2a by uint_arith
    subgoal for x1 x1a x2a by uint_arith
    subgoal for x1 x1a x2a by uint_arith
    subgoal for x1 x1a x2a by uint_arith
    subgoal for x1 x1a x2a by uint_arith
    subgoal for x1 x1a x2a  \<comment> \<open>Goal 9: unat (x1a + 1) \<le> 5 under x1a < 5\<close>
      apply (subgoal_tac "unat x1a < 5")
       prefer 2 apply (simp add: word_less_nat_alt)
      apply (subst unat_word_ariths(1))
      apply simp
      done
    subgoal for x1 x1a x2a  \<comment> \<open>Goal 10: measure strict decrease\<close>
      apply (subgoal_tac "unat x1a < 5")
       prefer 2 apply (simp add: word_less_nat_alt)
      apply (subst unat_word_ariths(1))
      apply simp
      done
    done
  done

(* Helper: x < y (as 32-word) implies unat (x + 1) = unat x + 1 (no wrap). *)
lemma unat_x_plus_1:
  fixes x :: "32 word"
  assumes "x < y"
  shows "unat (x + 1) = unat x + 1"
proof -
  have x_le: "unat x < unat y" using assms by (simp add: word_less_nat_alt)
  have y_le: "unat y \<le> 2 ^ 32 - 1" using unat_lt2p[of y] by simp
  have "unat x + 1 < 2 ^ 32" using x_le y_le by simp
  thus ?thesis by (subst unat_word_ariths(1)) simp
qed

lemma word_plus_one_le_of_less:
  fixes x y :: "32 word"
  assumes "x < y"
  shows "x + 1 \<le> y"
  using assms unat_x_plus_1[OF assms]
  by (simp add: word_less_nat_alt word_le_nat_alt)

(*
  Full functional-correctness spec for read_varint'. Relates the returned
  value/cursor to varint_decode on the heap_bytes view of the buffer.

  Under buffer validity and pos \<le> len, the function terminates with
  Result v such that (letting bytes = heap_bytes s buf (unat len)):
    case varint_decode (drop (unat pos) bytes) of
      Some (nv, rest) \<Rightarrow> pr_t_C.err_C v = VCD_OK
                         \<and> pr_t_C.pos_C v = len - of_nat (length rest)
                         \<and> unat (pr_t_C.val_C v) = nv
    | None           \<Rightarrow> pr_t_C.err_C v \<noteq> VCD_OK

  Body has 16 subgoals — 10 of them (bounds/IS_VALID/measure) are closed
  using the same pattern as read_varint'_bounded. The remaining 6 are
  the substantive work: relating read_varint's per-iteration state to
  varint_decode_loop via varint_acc_step + varint_overflow_check_nat.
*)

(* Helper: heap_bytes drop relation — dropping unat cur from the buffer
   is the same as dropping unat i elements from drop unat pos. *)
lemma heap_bytes_drop_shift:
  assumes "unat pos + i \<le> unat len"
  shows "drop (unat pos + i) (heap_bytes s buf (unat len))
       = drop i (drop (unat pos) (heap_bytes s buf (unat len)))"
  by (simp add: drop_drop add.commute)

(* When i < length, drop i xs = xs ! i # drop (Suc i) xs. *)
lemma heap_bytes_drop_Cons:
  assumes "i < unat len"
  shows "drop i (heap_bytes s buf (unat len))
       = heap_w8 s (buf +\<^sub>p int i) # drop (Suc i) (heap_bytes s buf (unat len))"
proof -
  have len: "length (heap_bytes s buf (unat len)) = unat len"
    by simp
  have nth: "heap_bytes s buf (unat len) ! i = heap_w8 s (buf +\<^sub>p int i)"
    using assms by (rule heap_bytes_nth)
  show ?thesis
    using assms len nth Cons_nth_drop_Suc[of i "heap_bytes s buf (unat len)"]
    by simp
qed

(*
  Attempt: full functional spec. Result-side case analysis drives the
  top-level shape; invariant relates C state to varint_decode_loop.
*)
lemma read_varint'_spec:
  assumes buf_ok: "buf_valid s buf (unat len)"
      and pos_ok: "pos \<le> len"
  shows "read_varint' buf len pos \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and>
                  (\<exists>v. r = Result v \<and>
                       pos \<le> pr_t_C.pos_C v \<and> pr_t_C.pos_C v \<le> len \<and>
                       (case varint_decode (drop (unat pos) (heap_bytes s buf (unat len))) of
                          Some (nv, rest) \<Rightarrow>
                             pr_t_C.err_C v = VCD_OK \<and>
                             unat (pr_t_C.pos_C v) = unat len - length rest \<and>
                             nv = unat (pr_t_C.val_C v)
                        | None \<Rightarrow>
                             pr_t_C.err_C v \<noteq> VCD_OK)) \<rbrace>"
  unfolding read_varint'_def
  apply (runs_to_vcg)
  apply (rule runs_to_whileLoop_exn [
    where I = "\<lambda>r t. t = s \<and>
                     (let bytes = heap_bytes s buf (unat len);
                          decoded = varint_decode (drop (unat pos) bytes)
                      in case r of
                         Result (cur, i, v) \<Rightarrow>
                           pos \<le> cur \<and> cur \<le> len \<and> unat i \<le> 5 \<and>
                           unat v < 2 ^ (7 * unat i) \<and>
                           unat cur = unat pos + unat i \<and>
                           varint_decode_loop (5 - unat i) (unat v)
                             (drop (unat cur) bytes) = decoded
                       | Exn e \<Rightarrow>
                           pos \<le> pr_t_C.pos_C e \<and>
                           pr_t_C.pos_C e \<le> len \<and>
                           (pr_t_C.err_C e = VCD_OK
                              \<longrightarrow> (\<exists>rest. decoded = Some (unat (pr_t_C.val_C e), rest)
                                        \<and> unat (pr_t_C.pos_C e) = unat len - length rest)) \<and>
                           (pr_t_C.err_C e \<noteq> VCD_OK \<longrightarrow> decoded = None))"
      and R = "measure (\<lambda>((cur, i, v), _). 5 - unat i)"])
  subgoal by simp  \<comment> \<open>wf measure\<close>
  subgoal \<comment> \<open>initial invariant: cur = pos, i = 0, v = 0, fuel = 5 matches top-level\<close>
    using pos_ok
    by (simp add: varint_decode_def Let_def)
  subgoal
    \<comment> \<open>Result post: fall-through path (x1a = 5 since unat x1a \<le> 5 and
        \<not> x1a < 5). Invariant's loop-equality with fuel 0 forces
        varint_decode to be None; err = VCD_ERR_VARINT \<noteq> VCD_OK.\<close>
    apply (clarsimp simp: Let_def split: prod.splits)
    apply (subgoal_tac "unat x1a = 5")
     prefer 2 apply (simp add: word_less_nat_alt)
    apply (simp add: varint_decode_loop_no_fuel)
    done
  subgoal
    \<comment> \<open>Exn post: Exn invariant contains err-dispatched Some/None cases;
        outer post wants the inverse case-split on decoded. Prove via
        contradiction in each of the two directions.\<close>
    apply (clarsimp simp: Let_def split: prod.splits option.splits)
    apply (intro conjI)
     apply auto
    done
  subgoal
    apply (simp add: Let_def split: prod.splits del: if_split)
    apply safe
    apply runs_to_vcg
    \<comment> \<open>Goal 1: truncation-throw — varint_decode = None.\<close>
    subgoal for cur i v
      apply (subgoal_tac "varint_decode_loop (5 - unat i) (unat v) [] = None")
       apply simp
      apply (cases "5 - unat i"; simp)
      done
    \<comment> \<open>Goal 2: IS_VALID (overflow-read, given \<not> len \<le> x1).\<close>
    subgoal for x1 x1a x2a
      using buf_validD[OF buf_ok, of "unat x1"]
      apply (subgoal_tac "x1 < len")
       apply (simp only: uint_nat)
       apply (simp add: word_less_nat_alt)
      apply simp
      done
    \<comment> \<open>Goal 3: pos \<le> x1+1 (overflow throw).\<close>
    subgoal for x1 x1a x2a by uint_arith
    \<comment> \<open>Goal 4: x1+1 \<le> len (overflow throw).\<close>
    subgoal for x1 x1a x2a by uint_arith
    \<comment> \<open>Goal 5: overflow-throw — varint_decode = None.
        varint_overflow_check_nat gives v \<ge> 2^25; varint_bound_forces_i_4
        gives i = 4; then 5 - i = 1; varint_decode_loop_fuel1_overflow
        gives None.\<close>
    subgoal for x1 x1a x2a
      apply (subgoal_tac "2 ^ 25 \<le> unat x2a")
       prefer 2 using varint_overflow_check_nat[of x2a] apply simp
      apply (subgoal_tac "unat x1a = 4")
       prefer 2 using varint_bound_forces_i_4 apply blast
      apply (subgoal_tac "varint_decode_loop 1 (unat x2a)
                            (drop (unat pos + 4) (heap_bytes s buf (unat len)))
                          = None")
       apply simp
      apply (rule varint_decode_loop_fuel1_overflow)
      apply simp
      done
    \<comment> \<open>Goal 6: pos \<le> x1+1 (success path).\<close>
    subgoal for x1 x1a x2a by uint_arith
    \<comment> \<open>Goal 7: x1+1 \<le> len (success path).\<close>
    subgoal for x1 x1a x2a by uint_arith
    \<comment> \<open>Goal 8: success post — varint_decode = Some (val_C, rest).
        Mirror of Goal 14: on continuation bit CLEAR, the loop returns
        Some(new_v, rest) via varint_decode_loop_step_success.\<close>
    subgoal premises prems for x1 x1a x2a
    proof -
      let ?bytes = "heap_bytes s buf (unat len)"
      let ?b = "heap_w8 s (buf +\<^sub>p uint x1)"
      have x1a_lt: "unat x1a < 5" using prems by (simp add: word_less_nat_alt)
      have i_plus_1: "unat (x1a + 1) = unat x1a + 1"
        using x1a_lt by (simp add: unat_word_ariths)
      have x1_lt_len: "unat x1 < unat len"
      proof -
        have le: "x1 \<le> len" using prems by simp
        have ne: "x1 \<noteq> len" using prems by auto
        from le ne have "x1 < len" by (simp add: less_le)
        thus ?thesis by (simp add: word_less_nat_alt)
      qed
      have x1_plus_1: "unat (x1 + 1) = unat x1 + 1"
      proof -
        have "x1 < len" using prems by (simp add: less_le)
        thus ?thesis by (rule unat_x_plus_1)
      qed
      have b_hi_clr: "?b AND 0x80 = 0"
        using prems by (simp add: ucast_and_0x80_eq_zero)
      have addr_eq: "(buf +\<^sub>p uint x1) = (buf +\<^sub>p int (unat x1))"
        by (simp only: uint_nat)
      have suc_eq: "Suc (unat x1) = unat x1 + 1" by simp
      have cons_eq: "drop (unat x1) ?bytes
                   = ?b # drop (unat x1 + 1) ?bytes"
      proof -
        have step: "drop (unat x1) ?bytes
                  = heap_w8 s (buf +\<^sub>p int (unat x1))
                    # drop (Suc (unat x1)) ?bytes"
          using x1_lt_len by (rule heap_bytes_drop_Cons)
        show ?thesis
          by (simp only: step addr_eq[symmetric] suc_eq)
      qed
      have v_bd: "unat x2a < 2 ^ (7 * unat x1a)" using prems by simp
      have ovf_nat: "unat x1a = 4 \<longrightarrow> x2a AND 0xFE000000 = 0"
      proof
        assume eq4: "unat x1a = 4"
        have "unat x1a = unat (4 :: 32 word)" using eq4 by simp
        hence "x1a = 4" using word_unat_eq_iff[of x1a 4] by simp
        with prems show "x2a AND 0xFE000000 = 0" by simp
      qed
      have step: "varint_decode_loop (5 - unat x1a) (unat x2a)
                    (?b # drop (unat x1 + 1) ?bytes)
                = Some (unat ((x2a << 7)
                            OR UCAST(8 \<rightarrow> 32) (?b AND 0x7F)),
                        drop (unat x1 + 1) ?bytes)"
        by (rule varint_decode_loop_step_success[OF v_bd x1a_lt ovf_nat b_hi_clr])
      have x1_eq: "unat x1 = unat pos + unat x1a" using prems by simp
      have inv: "varint_decode_loop (5 - unat x1a) (unat x2a)
                   (drop (unat x1) ?bytes)
               = varint_decode (drop (unat pos) ?bytes)"
        using prems x1_eq by simp
      have decode_some: "varint_decode (drop (unat pos) ?bytes)
                       = Some (unat ((x2a << 7)
                                   OR UCAST(8 \<rightarrow> 32) (?b AND 0x7F)),
                               drop (unat x1 + 1) ?bytes)"
        using inv cons_eq step by simp
      \<comment> \<open>Rest length: unat len - unat x1 - 1, and unat (x1+1) = unat x1 + 1.\<close>
      have rest_len: "length (drop (unat x1 + 1) ?bytes) = unat len - (unat x1 + 1)"
        by simp
      have cursor_eq: "unat (x1 + 1) = unat len - length (drop (unat x1 + 1) ?bytes)"
        using x1_lt_len x1_plus_1 rest_len by simp
      have ucast_eq: "(UCAST(8 \<rightarrow> 32) ?b AND 0x7F) = UCAST(8 \<rightarrow> 32) (?b AND 0x7F)"
        by (simp only: ucast_and_0x7F)
      show ?thesis
      proof
        show "varint_decode (drop (unat pos) ?bytes)
              = Some (unat ((x2a << 7)
                          OR UCAST(8 \<rightarrow> 32) ?b AND 0x7F),
                      drop (unat x1 + 1) ?bytes)
              \<and> unat (x1 + 1) = unat len - length (drop (unat x1 + 1) ?bytes)"
          using decode_some cursor_eq ucast_eq by simp
      qed
    qed
    \<comment> \<open>Goal 9: pos \<le> x1+1 (continue path).\<close>
    subgoal for x1 x1a x2a by uint_arith
    \<comment> \<open>Goal 10: x1+1 \<le> len (continue path).\<close>
    subgoal for x1 x1a x2a by uint_arith
    \<comment> \<open>Goal 11: unat (x1a + 1) \<le> 5 (continue: x1a < 5 so x1a + 1 \<le> 5).\<close>
    subgoal for x1 x1a x2a
      apply (subgoal_tac "unat x1a < 5")
       prefer 2 apply (simp add: word_less_nat_alt)
      apply (subst unat_word_ariths(1))
      apply simp
      done
    \<comment> \<open>Goal 12: unat v' < 2 ^ (7 * unat (x1a+1)) via varint_acc_step_bound_or,
        keeping the bound in the `7 * (unat i + 1)` form the helper needs.\<close>
    subgoal for x1 x1a x2a
      apply (subgoal_tac "unat (x1a + 1) = unat x1a + 1")
       prefer 2 apply (rule unat_x_plus_1[where y = 5]; simp)
      apply (subgoal_tac "unat ((x2a << 7) OR UCAST(8 \<rightarrow> 32)
                             (heap_w8 s (buf +\<^sub>p uint x1)) AND 0x7F)
                          < 2 ^ (7 * (unat x1a + 1))")
       apply simp
      apply (rule varint_acc_step_bound_or)
        apply simp
       apply simp
      apply simp
      done
    \<comment> \<open>Goal 13: unat (x1 + 1) = unat pos + unat (x1a + 1).\<close>
    subgoal for x1 x1a x2a
      apply (subgoal_tac "unat (x1 + 1) = unat x1 + 1")
       apply (subgoal_tac "unat (x1a + 1) = unat x1a + 1")
        apply simp
       apply (rule unat_x_plus_1[where y = 5])
       apply simp
      apply (rule unat_x_plus_1[where y = len])
      apply (simp add: less_le)
      done
    \<comment> \<open>Goal 14: loop-eq preservation on continue.\<close>
    subgoal premises prems for x1 x1a x2a
    proof -
      let ?bytes = "heap_bytes s buf (unat len)"
      let ?b = "heap_w8 s (buf +\<^sub>p uint x1)"
      let ?newv = "(x2a << 7) OR UCAST(8 \<rightarrow> 32) (?b AND 0x7F)"
      have x1a_lt: "unat x1a < 5"
        using prems by (simp add: word_less_nat_alt)
      have i_plus_1: "unat (x1a + 1) = unat x1a + 1"
        using x1a_lt by (simp add: unat_word_ariths)
      have x1_lt_len: "unat x1 < unat len"
      proof -
        have le: "x1 \<le> len" using prems by simp
        have ne: "x1 \<noteq> len" using prems by auto
        from le ne have "x1 < len" by (simp add: less_le)
        thus ?thesis by (simp add: word_less_nat_alt)
      qed
      have x1_plus_1: "unat (x1 + 1) = unat x1 + 1"
      proof -
        have "x1 < len" using prems by (simp add: less_le)
        thus ?thesis by (rule unat_x_plus_1)
      qed
      have b_hi_set: "?b AND 0x80 \<noteq> 0"
        using prems by (simp add: ucast_and_0x80_eq_zero)
      have addr_eq: "(buf +\<^sub>p uint x1) = (buf +\<^sub>p int (unat x1))"
        by (simp only: uint_nat)
      have suc_eq: "Suc (unat x1) = unat x1 + 1" by simp
      have cons_eq: "drop (unat x1) ?bytes
                   = ?b # drop (unat x1 + 1) ?bytes"
      proof -
        have step: "drop (unat x1) ?bytes
                  = heap_w8 s (buf +\<^sub>p int (unat x1))
                    # drop (Suc (unat x1)) ?bytes"
          using x1_lt_len by (rule heap_bytes_drop_Cons)
        show ?thesis
          by (simp only: step addr_eq[symmetric] suc_eq)
      qed
      have x1_eq: "unat x1 = unat pos + unat x1a" using prems by simp
      have inv: "varint_decode_loop (5 - unat x1a) (unat x2a) (drop (unat x1) ?bytes)
               = varint_decode (drop (unat pos) ?bytes)"
        using prems x1_eq by simp
      have v_bd: "unat x2a < 2 ^ (7 * unat x1a)" using prems by simp
      have ovf_nat: "unat x1a = 4 \<longrightarrow> x2a AND 0xFE000000 = 0"
      proof
        assume eq4: "unat x1a = 4"
        have "unat x1a = unat (4 :: 32 word)" using eq4 by simp
        hence "x1a = 4" using word_unat_eq_iff[of x1a 4] by simp
        with prems show "x2a AND 0xFE000000 = 0" by simp
      qed
      have step: "varint_decode_loop (5 - unat x1a) (unat x2a) (?b # drop (unat x1 + 1) ?bytes)
                = varint_decode_loop (5 - (unat x1a + 1))
                    (unat ((x2a << 7) OR UCAST(8 \<rightarrow> 32) (?b AND 0x7F)))
                    (drop (unat x1 + 1) ?bytes)"
        by (rule varint_decode_loop_step_continue[OF v_bd x1a_lt ovf_nat b_hi_set])
      have lhs: "varint_decode_loop (5 - (unat x1a + 1))
                   (unat ((x2a << 7) OR UCAST(8 \<rightarrow> 32) (?b AND 0x7F)))
                   (drop (unat x1 + 1) ?bytes)
               = varint_decode (drop (unat pos) ?bytes)"
        using step cons_eq inv by simp
      have drop_eq: "drop (unat (x1 + 1)) ?bytes = drop (unat x1 + 1) ?bytes"
        by (simp only: x1_plus_1)
      have fuel_eq: "5 - unat (x1a + 1) = 5 - (unat x1a + 1)"
        by (simp only: i_plus_1)
      have uint_simp: "(buf +\<^sub>p uint x1) = (buf +\<^sub>p int (unat x1))"
        by (simp only: uint_nat)
      \<comment> \<open>Put it all together. Goal LHS uses:
          varint_decode_loop (5 - unat (x1a + 1))
            (unat ((x2a << 7) OR UCAST(8\<rightarrow>32) (heap_w8 s (buf +_p uint x1)) AND 0x7F))
            (drop (unat (x1 + 1)) ?bytes)
          = varint_decode (drop (unat pos) ?bytes). \<close>
      have v_eq: "(UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p uint x1)) AND 0x7F)
                 = UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p uint x1) AND 0x7F)"
        by (simp only: ucast_and_0x7F)
      have lhs': "varint_decode_loop (5 - unat (x1a + 1))
                    (unat ((x2a << 7) OR UCAST(8 \<rightarrow> 32)
                             (heap_w8 s (buf +\<^sub>p uint x1)) AND 0x7F))
                    (drop (unat (x1 + 1)) ?bytes)
                = varint_decode_loop (5 - (unat x1a + 1))
                    (unat ((x2a << 7) OR UCAST(8 \<rightarrow> 32) (?b AND 0x7F)))
                    (drop (unat x1 + 1) ?bytes)"
        by (simp only: v_eq drop_eq fuel_eq)
      show ?thesis
        using lhs' lhs by simp
    qed
    \<comment> \<open>Goal 15: measure strict decrease.\<close>
    subgoal for x1 x1a x2a
      apply (subgoal_tac "unat x1a < 5")
       prefer 2 apply (simp add: word_less_nat_alt)
      apply (subst unat_word_ariths(1))
      apply simp
      done
    done
  done

lemma read_varint'_succeeds:
  assumes "buf_valid s buf (unat len)" "pos \<le> len"
  shows "succeeds (read_varint' buf len pos) s"
  using read_varint'_spec[OF assms]
  by (simp add: succeeds_runs_to_iff runs_to_weaken)

lemma read_varint'_reaches_state:
  assumes "buf_valid s buf (unat len)" "pos \<le> len"
      and "reaches (read_varint' buf len pos) s r t"
  shows "t = s"
proof -
  from assms(3) have succ: "succeeds (read_varint' buf len pos) s"
    by (rule reaches_succeeds)
  from read_varint'_spec[OF assms(1,2)]
  have rt: "read_varint' buf len pos \<bullet> s \<lbrace> \<lambda>r t. t = s \<and>
    (\<exists>v. r = Result v \<and> pos \<le> pr_t_C.pos_C v \<and> pr_t_C.pos_C v \<le> len \<and>
         (case varint_decode (drop (unat pos) (heap_bytes s buf (unat len))) of
            Some (nv, rest) \<Rightarrow> pr_t_C.err_C v = VCD_OK \<and>
              unat (pr_t_C.pos_C v) = unat len - length rest \<and> nv = unat (pr_t_C.val_C v)
          | None \<Rightarrow> pr_t_C.err_C v \<noteq> VCD_OK)) \<rbrace>" .
  from runs_toD2[OF rt assms(3)] show "t = s" by auto
qed

lemma read_varint'_reaches_pos:
  assumes "buf_valid s buf (unat len)" "pos \<le> len"
      and "reaches (read_varint' buf len pos) s (Result v) t"
  shows "pr_t_C.pos_C v \<le> len"
proof -
  from read_varint'_spec[OF assms(1,2)]
  have rt: "read_varint' buf len pos \<bullet> s \<lbrace> \<lambda>r t. t = s \<and>
    (\<exists>v. r = Result v \<and> pos \<le> pr_t_C.pos_C v \<and> pr_t_C.pos_C v \<le> len \<and>
         (case varint_decode (drop (unat pos) (heap_bytes s buf (unat len))) of
            Some (nv, rest) \<Rightarrow> pr_t_C.err_C v = VCD_OK \<and>
              unat (pr_t_C.pos_C v) = unat len - length rest \<and> nv = unat (pr_t_C.val_C v)
          | None \<Rightarrow> pr_t_C.err_C v \<noteq> VCD_OK)) \<rbrace>" .
  from runs_toD2[OF rt assms(3)] show ?thesis by auto
qed

(* ---------- build_code_table refinement ---------- *)

(*
  build_code_table' has no failure branches — only guarded array writes.
  Under the simplest precondition (no precondition needed on state), it
  terminates with a Result () and modifies only the code_tbl and
  code_tbl_built fields. Full functional refinement (relating the
  resulting code_tbl to default_entry) is TODO.

  Six nested whileLoops, each writing specific code_tbl[idx][slot]
  entries. The top-level Hoare triple we want is:
    {{ True }} build_code_table' () {{ \<lambda>_ s'. code_tbl_built_'' s' = 1 }}
  combined with a functional relation over code_tbl_'' s'.
*)

(*
  Helper: if a word pos satisfies pos \<le> len and unat pos = unat len - k,
  then pos = len - word_of_nat k.
*)
lemma word_eq_sub_of_nat:
  fixes pos len :: "'a::len word"
  assumes "pos \<le> len"
      and "unat pos = unat len - k"
      and "k \<le> unat len"
  shows "pos = len - of_nat k"
proof -
  have k_lt: "k < 2 ^ LENGTH('a)"
    using assms(3) unat_lt2p[of len] by (simp add: less_le)
  have unat_k: "unat (of_nat k :: 'a word) = k"
    using k_lt by (simp add: unat_of_nat_eq)
  have "unat (len - of_nat k) = unat len - unat (of_nat k :: 'a word)"
    using assms(3) unat_k
    by (simp add: unat_sub word_le_nat_alt)
  also have "\<dots> = unat len - k" by (simp add: unat_k)
  also have "\<dots> = unat pos" using assms(2) by simp
  finally show ?thesis by (metis word_unat_eq_iff)
qed

(*
  Helper: the C SAME-mode slot computation
     slot = 0xFFFFFA00 + mode * 0x100 + UCAST(8\<rightarrow>32) byte
  lies in [0, 0x300) when mode \<in> {6,7,8}. Observe that
     0xFFFFFA00 + mode * 0x100 = (mode - 6) * 0x100    (mod 2\<^sup>3\<^sup>2),
  so unfolded in nats, slot = (unat mode - 6) * 256 + unat byte, which is
  in [0, 768) = [0, 0x300) because byte < 256.

  We compute unat slot in the natural-number model, then compare 0x300.
*)
lemma unat_same_slot_word:
  fixes mode :: "32 word" and byte :: "8 word"
  assumes "unat mode \<in> {6, 7, 8}"
  shows "unat (0xFFFFFA00 + mode * 0x100 + UCAST(8 \<rightarrow> 32) byte)
         = (unat mode - 6) * 256 + unat byte"
proof -
  have byte_lt': "unat byte < 256"
    using unat_lt2p[of byte] by simp
  have byte_unat: "unat (UCAST(8 \<rightarrow> 32) byte) = unat byte"
  proof -
    have "unat byte < 2 ^ 32" using byte_lt' by simp
    thus ?thesis by (simp add: unat_ucast)
  qed
  have byte_lt: "unat byte < 256"
    using unat_lt2p[of byte] by simp
  have mode_lt_9: "unat mode < 9" using assms by auto
  have mode_ge_6: "unat mode \<ge> 6" using assms by auto

  \<comment> \<open>mode * 0x100: no wrap since unat mode < 9 < 2^24.\<close>
  have m100_unat: "unat (mode * 0x100) = unat mode * 256"
  proof -
    have "unat mode * unat (0x100 :: 32 word) < 2 ^ 32"
      using mode_lt_9 by simp
    thus ?thesis by (simp add: unat_mult_lem[THEN iffD1])
  qed

  \<comment> \<open>mode * 0x100 < 0x900, so adding 0xFFFFFA00 wraps by exactly 2^32.\<close>
  have sum1_eq: "unat (0xFFFFFA00 + mode * 0x100)
                 = (0xFFFFFA00 + unat mode * 256) - 2 ^ 32"
  proof -
    have hi_lo: "unat (0xFFFFFA00 :: 32 word) = 0xFFFFFA00"
      by simp
    have sum_bound: "0xFFFFFA00 + unat mode * 256 \<ge> 2 ^ 32"
      using mode_ge_6 by (simp; arith)
    have sum_under: "0xFFFFFA00 + unat mode * 256 < 2 * 2 ^ 32"
      using mode_lt_9 by (simp; arith)
    have "unat (0xFFFFFA00 + mode * 0x100)
          = (unat (0xFFFFFA00 :: 32 word) + unat (mode * 0x100)) mod 2 ^ 32"
      by (simp add: unat_word_ariths(1))
    also have "\<dots> = (0xFFFFFA00 + unat mode * 256) mod 2 ^ 32"
      by (simp add: hi_lo m100_unat)
    also have "\<dots> = (0xFFFFFA00 + unat mode * 256) - 2 ^ 32"
      using sum_bound sum_under by (simp add: mod_nat_eqI)
    finally show ?thesis .
  qed

  \<comment> \<open>Final sum + byte: stays well below 2^32, so no further wrap.\<close>
  have inner_lt: "(0xFFFFFA00 + unat mode * 256) - 2 ^ 32 + unat byte < 2 ^ 32"
    using mode_lt_9 byte_lt by (simp; arith)
  have "unat (0xFFFFFA00 + mode * 0x100 + UCAST(8 \<rightarrow> 32) byte)
        = (unat (0xFFFFFA00 + mode * 0x100) + unat (UCAST(8 \<rightarrow> 32) byte))
          mod 2 ^ 32"
    by (simp add: unat_word_ariths(1))
  also have "\<dots> = ((0xFFFFFA00 + unat mode * 256) - 2 ^ 32 + unat byte) mod 2 ^ 32"
    by (simp add: sum1_eq byte_unat)
  also have "\<dots> = (0xFFFFFA00 + unat mode * 256) - 2 ^ 32 + unat byte"
    using inner_lt by simp
  also have "\<dots> = (unat mode - 6) * 256 + unat byte"
    using mode_ge_6 by (simp; arith)
  finally show ?thesis .
qed

lemma same_slot_bound:
  fixes mode :: "32 word" and byte :: "8 word"
  assumes "unat mode \<in> {6, 7, 8}"
  shows "0xFFFFFA00 + mode * 0x100 + UCAST(8 \<rightarrow> 32) byte < (0x300 :: 32 word)"
proof -
  have byte_lt: "unat byte < 256" using unat_lt2p[of byte] by simp
  have mode_lt_9: "unat mode < 9" using assms by auto
  have "unat (0xFFFFFA00 + mode * 0x100 + UCAST(8 \<rightarrow> 32) byte)
        = (unat mode - 6) * 256 + unat byte"
    by (rule unat_same_slot_word[OF assms])
  also have "\<dots> < 768"
    using mode_lt_9 byte_lt by (simp; arith)
  finally show ?thesis by (simp add: word_less_nat_alt)
qed

lemma read_varint'_at_end_nonok:
  assumes buf_ok: "buf_valid s buf (unat len)"
  shows "read_varint' buf len len \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and> (\<exists>v. r = Result v \<and> pr_t_C.err_C v \<noteq> VCD_OK) \<rbrace>"
proof -
  have le_len: "len \<le> len" by simp
  have drop_nil: "drop (unat len) (heap_bytes s buf (unat len)) = []"
    by simp
  have vd_none: "varint_decode (drop (unat len) (heap_bytes s buf (unat len))) = None"
  proof -
    have "varint_decode_loop 5 0 ([] :: byte list) = varint_decode_loop (Suc 4) 0 ([] :: byte list)"
      by simp
    also have "\<dots> = None"
      by (rule varint_decode_loop.simps(2))
    finally show ?thesis
      unfolding drop_nil varint_decode_def .
  qed
  show ?thesis
    apply (rule runs_to_weaken[OF read_varint'_spec[OF buf_ok le_len]])
    using vd_none
    apply (clarsimp split: option.splits)
    done
qed

(*
  AutoCorres lifts `near_arr` / `same_arr` as record fields of
  `lifted_globals`, of array type. They are indexed via `.[unat i]`
  (the Arrays.index abbreviation `arr.[n]`). No heap-pointer
  validity is required — the arrays are part of the state record.

  The pure spec models them as nat lists. cache_abs relates the two:
    - The `near_ptr` is the C record's `near_ptr_C` field value,
      supplied by the caller of decode_address (passed in as a
      parameter, not a global).
    - near_arr_'' s has length 4; same_arr_'' s has length 768
      (statically, from the Arrays.array index type).

  Under cache_abs, the `near c` and `same c` lists coincide with
  the array contents once coerced to nat.
*)

definition cache_abs :: "lifted_globals \<Rightarrow> cache \<Rightarrow> 32 word \<Rightarrow> bool" where
  "cache_abs s c np =
     (length (near c) = s_near \<and>
      length (same c) = same_buckets \<and>
      unat np < s_near \<and>
      near_ptr c = unat np \<and>
      (\<forall>i < s_near. near_arr_'' s .[i] = of_nat (near c ! i)) \<and>
      (\<forall>i < same_buckets. same_arr_'' s .[i] = of_nat (same c ! i)))"

(*
  Well-formedness of a cache: entries all fit in 32 bits, so nat/word
  round-trip doesn't lose information. Needed when writing addr back
  into the array and matching the pure `cache_update`.
*)
definition cache_wf :: "cache \<Rightarrow> bool" where
  "cache_wf c =
     (length (near c) = s_near \<and>
      length (same c) = same_buckets \<and>
      near_ptr c < s_near \<and>
      (\<forall>i < s_near. near c ! i < 2 ^ 32) \<and>
      (\<forall>i < same_buckets. same c ! i < 2 ^ 32))"

lemma cache_abs_wf:
  assumes "cache_abs s c np"
  shows "length (near c) = s_near
       \<and> length (same c) = same_buckets
       \<and> near_ptr c < s_near"
  using assms
  by (auto simp add: cache_abs_def word_less_nat_alt s_near_def)

(*
  cache_abs is functional in c: given the same state and near_ptr word,
  any two cache_wf caches abstracting to them must be equal.  Used to
  prove dst_prev = dst in the loop-invariant advance lemma.
*)
lemma cache_abs_unique:
  assumes a1: "cache_abs t c1 np"
      and w1: "cache_wf c1"
      and a2: "cache_abs t c2 np"
      and w2: "cache_wf c2"
  shows "c1 = c2"
proof -
  have np_eq: "near_ptr c1 = near_ptr c2"
    using a1 a2 unfolding cache_abs_def by simp
  have len_near1: "length (near c1) = s_near"
    using a1 unfolding cache_abs_def by simp
  have len_near2: "length (near c2) = s_near"
    using a2 unfolding cache_abs_def by simp
  have len_same1: "length (same c1) = same_buckets"
    using a1 unfolding cache_abs_def by simp
  have len_same2: "length (same c2) = same_buckets"
    using a2 unfolding cache_abs_def by simp
  have near_arr_1: "\<forall>i. i < s_near \<longrightarrow> near_arr_'' t .[i] = of_nat (near c1 ! i)"
    using a1 unfolding cache_abs_def by simp
  have near_arr_2: "\<forall>i. i < s_near \<longrightarrow> near_arr_'' t .[i] = of_nat (near c2 ! i)"
    using a2 unfolding cache_abs_def by simp
  have same_arr_1: "\<forall>i. i < same_buckets \<longrightarrow> same_arr_'' t .[i] = of_nat (same c1 ! i)"
    using a1 unfolding cache_abs_def by simp
  have same_arr_2: "\<forall>i. i < same_buckets \<longrightarrow> same_arr_'' t .[i] = of_nat (same c2 ! i)"
    using a2 unfolding cache_abs_def by simp
  have bnd_near1: "\<forall>i. i < s_near \<longrightarrow> near c1 ! i < 2^32"
    using w1 unfolding cache_wf_def by simp
  have bnd_near2: "\<forall>i. i < s_near \<longrightarrow> near c2 ! i < 2^32"
    using w2 unfolding cache_wf_def by simp
  have bnd_same1: "\<forall>i. i < same_buckets \<longrightarrow> same c1 ! i < 2^32"
    using w1 unfolding cache_wf_def by simp
  have bnd_same2: "\<forall>i. i < same_buckets \<longrightarrow> same c2 ! i < 2^32"
    using w2 unfolding cache_wf_def by simp
  have near_eq: "near c1 = near c2"
  proof (rule nth_equalityI)
    show "length (near c1) = length (near c2)"
      using len_near1 len_near2 by simp
  next
    fix i assume i_lt: "i < length (near c1)"
    hence i_sn: "i < s_near" using len_near1 by simp
    have w_eq: "(of_nat (near c1 ! i) :: 32 word) = of_nat (near c2 ! i)"
      using near_arr_1 near_arr_2 i_sn by metis
    have b1: "near c1 ! i < 2^32" using bnd_near1 i_sn by simp
    have b2: "near c2 ! i < 2^32" using bnd_near2 i_sn by simp
    have unat_eq: "unat ((of_nat (near c1 ! i)) :: 32 word) =
                    unat ((of_nat (near c2 ! i)) :: 32 word)"
      using w_eq by simp
    have u1: "unat ((of_nat (near c1 ! i)) :: 32 word) = near c1 ! i"
      using b1 by (simp add: unat_of_nat_eq)
    have u2: "unat ((of_nat (near c2 ! i)) :: 32 word) = near c2 ! i"
      using b2 by (simp add: unat_of_nat_eq)
    from unat_eq u1 u2 show "near c1 ! i = near c2 ! i" by argo
  qed
  have same_eq: "same c1 = same c2"
  proof (rule nth_equalityI)
    show "length (same c1) = length (same c2)"
      using len_same1 len_same2 by simp
  next
    fix i assume i_lt: "i < length (same c1)"
    hence i_sb: "i < same_buckets" using len_same1 by simp
    have w_eq: "(of_nat (same c1 ! i) :: 32 word) = of_nat (same c2 ! i)"
      using same_arr_1 same_arr_2 i_sb by metis
    have b1: "same c1 ! i < 2^32" using bnd_same1 i_sb by simp
    have b2: "same c2 ! i < 2^32" using bnd_same2 i_sb by simp
    have unat_eq: "unat ((of_nat (same c1 ! i)) :: 32 word) =
                    unat ((of_nat (same c2 ! i)) :: 32 word)"
      using w_eq by simp
    have u1: "unat ((of_nat (same c1 ! i)) :: 32 word) = same c1 ! i"
      using b1 by (simp add: unat_of_nat_eq)
    have u2: "unat ((of_nat (same c2 ! i)) :: 32 word) = same c2 ! i"
      using b2 by (simp add: unat_of_nat_eq)
    from unat_eq u1 u2 show "same c1 ! i = same c2 ! i" by argo
  qed
  show ?thesis
    using np_eq near_eq same_eq
    by (cases c1; cases c2; simp)
qed

(*
  Mirror for the pure cache_update. Writing `addr` at slot `np` of
  near_arr and at `addr mod same_buckets` of same_arr preserves cache_abs.

  Parameters tracked: new near_ptr becomes (np + 1) mod 4 which is
  (near_ptr c + 1) mod s_near by cache_abs.
*)
lemma cache_abs_update:
  assumes abs: "cache_abs s c np"
      and np_lt: "np < 4"
  shows "cache_abs
           (same_arr_''_update
              (\<lambda>a. Arrays.update a (unat (w mod 0x300 :: 32 word)) w)
              (near_arr_''_update
                 (\<lambda>a. Arrays.update a (unat np) w)
                 s))
           (cache_update c (unat w))
           ((np + 1) mod 4)"
proof -
  let ?sb = "same_buckets"
  let ?addr = "unat w"
  let ?slot_w = "w mod 0x300 :: 32 word"
  let ?slot_n = "unat ?slot_w"
  let ?s' = "same_arr_''_update (\<lambda>a. Arrays.update a ?slot_n w)
               (near_arr_''_update (\<lambda>a. Arrays.update a (unat np) w) s)"
  let ?c' = "cache_update c ?addr"
  let ?np' = "(np + 1) mod (4 :: 32 word)"

  have len_near: "length (near c) = s_near" using abs cache_abs_def by auto
  have len_same: "length (same c) = ?sb" using abs cache_abs_def by auto
  have np_eq: "unat np = near_ptr c" using abs cache_abs_def by auto
  have np_lt_sn: "unat np < s_near" using abs cache_abs_def by auto
  have s_near_4: "s_near = 4" by (simp add: s_near_def)
  have sb_768: "?sb = 768" by (simp add: same_buckets_def s_same_def)
  have near_i: "\<forall>i. i < s_near \<longrightarrow> near_arr_'' s .[i] = of_nat (near c ! i)"
    using abs cache_abs_def by auto
  have same_i: "\<forall>i. i < ?sb \<longrightarrow> same_arr_'' s .[i] = of_nat (same c ! i)"
    using abs cache_abs_def by auto
  have w_as_of_nat: "(of_nat ?addr :: 32 word) = w" by simp

  \<comment> \<open>New near_ptr.\<close>
  have np_plus_1: "unat (np + 1) = unat np + 1"
    using np_lt unat_x_plus_1 by blast
  have np'_eq: "unat ?np' = (unat np + 1) mod 4"
    by (simp add: unat_mod np_plus_1)
  have np'_lt_sn: "unat ?np' < s_near" using np'_eq s_near_4 by simp
  have np'_eq_nearptr: "near_ptr ?c' = unat ?np'"
    by (simp add: cache_update_def np'_eq s_near_4 np_eq)

  \<comment> \<open>New cache field lengths.\<close>
  have near_len_new: "length (near ?c') = s_near"
    by (simp add: cache_update_def len_near)
  have same_len_new: "length (same ?c') = ?sb"
    by (simp add: cache_update_def len_same)

  \<comment> \<open>Near array contents after update.\<close>
  have near_slot_lt: "unat np < CARD(4)" using np_lt_sn s_near_4 by simp
  have near_arr_new:
    "near_arr_'' ?s' = Arrays.update (near_arr_'' s) (unat np) w"
    by simp
  have near_contents:
    "\<forall>i. i < s_near \<longrightarrow> near_arr_'' ?s' .[i] = of_nat (near ?c' ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < s_near"
    have i_lt_4: "i < CARD(4)" using i_lt s_near_4 by simp
    show "near_arr_'' ?s' .[i] = of_nat (near ?c' ! i)"
    proof (cases "i = unat np")
      case True
      have "near_arr_'' ?s' .[i] = w"
        using True near_slot_lt near_arr_new
        by (simp add: Arrays.index_update i_lt_4)
      also have "\<dots> = of_nat (near ?c' ! i)"
        using True np_eq len_near np_lt_sn
        by (simp add: cache_update_def nth_list_update_eq)
      finally show ?thesis .
    next
      case False
      have "near_arr_'' ?s' .[i] = near_arr_'' s .[i]"
        using False near_arr_new i_lt_4
        by (simp add: index_update2)
      also have "\<dots> = of_nat (near c ! i)"
        using i_lt near_i by auto
      also have "\<dots> = of_nat (near ?c' ! i)"
        using False np_eq
        by (simp add: cache_update_def nth_list_update_neq)
      finally show ?thesis .
    qed
  qed

  \<comment> \<open>Same array contents after update.\<close>
  have slot_w_eq_n: "?slot_n = ?addr mod ?sb"
    by (simp add: unat_mod sb_768)
  have slot_n_lt_sb: "?slot_n < ?sb"
    by (simp add: slot_w_eq_n sb_768)
  have slot_n_lt_768: "?slot_n < CARD(768)"
    using slot_n_lt_sb sb_768 by simp
  have same_arr_new:
    "same_arr_'' ?s' = Arrays.update (same_arr_'' s) ?slot_n w"
    by simp
  have same_contents:
    "\<forall>i. i < ?sb \<longrightarrow> same_arr_'' ?s' .[i] = of_nat (same ?c' ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < ?sb"
    have i_lt_768: "i < CARD(768)" using i_lt sb_768 by simp
    show "same_arr_'' ?s' .[i] = of_nat (same ?c' ! i)"
    proof (cases "i = ?slot_n")
      case True
      have "same_arr_'' ?s' .[i] = w"
        using True slot_n_lt_768 same_arr_new
        by (simp add: index_update)
      also have "\<dots> = of_nat (same ?c' ! i)"
        using True slot_w_eq_n len_same slot_n_lt_sb
        by (simp add: cache_update_def nth_list_update_eq)
      finally show ?thesis .
    next
      case False
      have "same_arr_'' ?s' .[i] = same_arr_'' s .[i]"
        using False same_arr_new slot_n_lt_768 i_lt_768
        by (simp add: index_update2)
      also have "\<dots> = of_nat (same c ! i)"
        using i_lt same_i by auto
      also have "\<dots> = of_nat (same ?c' ! i)"
        using False slot_w_eq_n
        by (simp add: cache_update_def nth_list_update_neq)
      finally show ?thesis .
    qed
  qed

  show ?thesis
    unfolding cache_abs_def
    using near_len_new same_len_new np'_lt_sn np'_eq_nearptr
          near_contents same_contents
    by simp
qed

(*
  Hoare-triple contract for decode_address'. Follows the pure
  `decode_address` from AddressCache.thy. The AutoCorres lift uses
  `finally`, turning the success path into a throw carrying the
  final ar_t_C. So in the outer runs_to, a Result in fact means
  "control falls through without throwing" = the final mode 9+
  rejection path, and Exn carries the outcome (both success with
  err = 0 and failure with err \<noteq> 0).

  Precondition:
    - buf_valid on the patch buffer up to unat addr_end
    - pos \<le> addr_end
    - cache_abs s c np_in  (the np_in arg is passed via near_ptr parameter)
    - cache_wf c
    - unat mode < 9

  Postcondition (inverts Result/Exn because of `finally`):
    - s unchanged? NO — near_arr/same_arr are modified on success path.
      Only other fields are preserved.
    - If decode_address c (unat mode) (unat here) (drop (unat pos) bytes)
        = Some (addr, rest, c'), then the Exn result is
          ar_t_C (addr_end - of_nat (length rest)) (of_nat addr)
                 (of_nat (near_ptr c')) 0
        and s' satisfies cache_abs s' c' (of_nat (near_ptr c')).
    - If it's None, then the Exn result has err \<noteq> 0.
*)
lemma decode_address'_spec:
  assumes buf_ok: "buf_valid s patch (unat addr_end)"
      and pos_ok: "pos \<le> addr_end"
      and cache_ok: "cache_abs s c np_in"
      and cache_wf_ok: "cache_wf c"
      and mode_ok: "unat mode < 9"
      and here_ok: "unat here < 2 ^ 32"
  shows "decode_address' patch addr_end pos here mode np_in \<bullet> s
           \<lbrace> \<lambda>r s'.
              \<exists>ar. r = Result ar \<and>
                   (let bytes = heap_bytes s patch (unat addr_end);
                        decoded = decode_address c (unat mode) (unat here)
                                    (drop (unat pos) bytes)
                    in (case decoded of
                          Some (addr, rest, c') \<Rightarrow>
                            (if addr < 2 ^ 32
                             then ar_t_C.err_C ar = 0 \<and>
                                  ar_t_C.pos_C ar = addr_end - of_nat (length rest) \<and>
                                  ar_t_C.addr_C ar = of_nat addr \<and>
                                  unat (ar_t_C.near_ptr_C ar) < s_near \<and>
                                  near_ptr c' = unat (ar_t_C.near_ptr_C ar) \<and>
                                  cache_abs s' c' (ar_t_C.near_ptr_C ar)
                             else True)
                        | None \<Rightarrow> ar_t_C.err_C ar \<noteq> 0)) \<rbrace>"
  unfolding decode_address'_def
  apply runs_to_vcg
  (* 5 subgoals: mode = 0, mode = 1, NEAR (2..5), SAME (6..8), and mode \<ge> 9.
     The last is vacuous under mode_ok. *)
      prefer 5
      subgoal using mode_ok by (simp add: word_less_nat_alt)
     (* Mode 0: varint(addr). *)
     subgoal for x
       apply (rule runs_to_weaken[OF read_varint'_spec[OF buf_ok pos_ok]])
       apply (clarsimp split: option.splits)
         \<comment> \<open>Goal 0a: varint error \<Longrightarrow> decode_address = None \<Longrightarrow> err \<noteq> 0.
             Goal 0b: varint success, execute array writes + throw.\<close>
       subgoal for v e
         \<comment> \<open>varint None: decode_address c 0 _ bytes unfolds to varint_decode bytes = None.\<close>
         apply (clarsimp simp: decode_address_def)
         done
       subgoal for v b
         \<comment> \<open>varint Some (unat val, b): decode_address c 0 _ bytes
             = Some (unat val, b, cache_update c (unat val)).\<close>
         apply runs_to_vcg
         subgoal \<comment> \<open>guard: np_in < 4. From cache_abs: unat np_in < s_near = 4.\<close>
           using cache_ok
           by (simp add: cache_abs_def s_near_def word_less_nat_alt)
         subgoal \<comment> \<open>guard: val mod 0x300 < 0x300.\<close>
           by (simp add: word_mod_less_divisor)
         subgoal \<comment> \<open>(1) varint succeeded but decode_address = None \<Longrightarrow> contradiction.\<close>
           by (simp add: decode_address_def)
         subgoal for a aa ba \<comment> \<open>(2) pr_t_C.pos_C v = addr_end - of_nat (length aa).\<close>
           apply (clarsimp simp: decode_address_def)
           apply (rule word_eq_sub_of_nat[where k = "length aa"])
             apply assumption
            apply simp
             \<comment> \<open>length aa \<le> unat addr_end:
                 length aa \<le> length (drop (unat pos) bytes) = unat addr_end - unat pos.\<close>
           apply (drule varint_decode_length)
           apply (simp add: word_le_nat_alt)
           done
         subgoal for a aa ba \<comment> \<open>(3) val_C v = word_of_nat a where a = unat (val_C v).\<close>
           apply (clarsimp simp add: decode_address_def)
           done
         subgoal for a aa ba \<comment> \<open>(4) unat ((np_in + 1) mod 4) < s_near.\<close>
           by (simp add: s_near_def unat_mod)
         subgoal for a aa ba \<comment> \<open>(5) near_ptr ba = unat (np_in + 1) mod 4.\<close>
           apply (clarsimp simp: decode_address_def cache_update_def)
           using cache_ok
           apply (clarsimp simp: cache_abs_def s_near_def word_less_nat_alt
                                 unat_mod unat_word_ariths(1))
           done
         subgoal for a aa ba \<comment> \<open>(6) cache_abs after array writes.\<close>
           apply (clarsimp simp: decode_address_def)
           apply (rule cache_abs_update[OF cache_ok])
           using cache_ok apply (simp add: cache_abs_def s_near_def
                                           word_less_nat_alt)
           done
         done
       done
     (* Mode 1: varint(here - addr). *)
    subgoal for x
      apply (rule runs_to_weaken[OF read_varint'_spec[OF buf_ok pos_ok]])
      apply (clarsimp split: option.splits)
      subgoal for v e
        \<comment> \<open>varint error path: decode_address returns None for None varint.\<close>
        by (clarsimp simp: decode_address_def)
      subgoal for v b
        apply runs_to_vcg
           \<comment> \<open>9 subgoals: (1) contradict Some in the here<val path, (2) np_in<4,
               (3) val mod 0x300, (4) contradict None in the here\<ge>val path,
               (5) pos_C, (6) addr_C, (7) unat mod, (8) near_ptr, (9) cache_abs.\<close>
        subgoal \<comment> \<open>(1) here < val_C v path, decode_address gave Some — contradiction.\<close>
          by (clarsimp simp: decode_address_def word_less_nat_alt)
        subgoal \<comment> \<open>(2) guard np_in < 4.\<close>
          using cache_ok
          by (simp add: cache_abs_def s_near_def word_less_nat_alt)
        subgoal \<comment> \<open>(3) guard val mod 0x300.\<close>
          by (simp add: word_mod_less_divisor)
        subgoal \<comment> \<open>(4) \<not>here<val path, decode_address gave None — contradiction.\<close>
          by (clarsimp simp: decode_address_def Let_def word_less_nat_alt)
        subgoal for a aa ba \<comment> \<open>(5) pos_C.\<close>
          apply (clarsimp simp: decode_address_def Let_def
                                split: if_splits)
          apply (rule word_eq_sub_of_nat[where k = "length aa"])
            apply assumption
           apply simp
          apply (drule varint_decode_length, simp add: word_le_nat_alt)
          done
        subgoal for a aa ba \<comment> \<open>(6) addr_C = word_of_nat a where a = unat here - unat val_C.\<close>
          by (clarsimp simp: decode_address_def Let_def word_less_nat_alt
                             of_nat_diff[symmetric, where 'a = "32 word"]
                             split: if_splits)
        subgoal \<comment> \<open>(7) unat ((np_in + 1) mod 4) < s_near.\<close>
          by (simp add: s_near_def unat_mod)
        subgoal \<comment> \<open>(8) near_ptr.\<close>
          apply (clarsimp simp: decode_address_def Let_def word_less_nat_alt
                                split: if_splits)
          using cache_ok
          apply (clarsimp simp: cache_abs_def cache_update_def s_near_def
                                unat_mod unat_word_ariths(1))
          done
        subgoal \<comment> \<open>(9) cache_abs after array writes.\<close>
          apply (clarsimp simp: decode_address_def Let_def word_less_nat_alt
                                split: if_splits)
          apply (subst unat_sub[symmetric])
           apply (simp add: word_le_nat_alt)
          apply (rule cache_abs_update[OF cache_ok])
          using cache_ok apply (simp add: cache_abs_def s_near_def
                                          word_less_nat_alt)
          done
        done
      done
     (* Mode NEAR (2..5): near_arr[mode - 2] + varint. *)
    subgoal for x
      apply (rule runs_to_weaken[OF read_varint'_spec[OF buf_ok pos_ok]])
      apply (clarsimp split: option.splits)
      subgoal for v e
        \<comment> \<open>varint error.\<close>
        by (auto simp: decode_address_def s_near_def s_same_def
                       word_less_nat_alt
                 split: if_splits)
      subgoal for v b
        apply runs_to_vcg
           \<comment> \<open>9 subgoals: guard mode-2<4, np<4, val mod, False on decode=None,
               pos_C, addr_C, unat mod, near_ptr, cache_abs.\<close>
        subgoal \<comment> \<open>(1) mode - 2 < 4.\<close>
          apply (subgoal_tac "(2 :: 32 word) \<le> mode")
           apply (simp add: word_less_nat_alt unat_sub)
          apply (simp add: word_le_nat_alt)
          apply (subgoal_tac "unat mode \<noteq> 0 \<and> unat mode \<noteq> 1")
           apply arith
          apply (simp add: unat_eq_0 word_unat_eq_iff[of mode 1])
          done
        subgoal \<comment> \<open>(2) np_in < 4.\<close>
          using cache_ok
          by (simp add: cache_abs_def s_near_def word_less_nat_alt)
        subgoal \<comment> \<open>(3) val mod 0x300.\<close>
          by (simp add: word_mod_less_divisor)
        subgoal \<comment> \<open>(4) decode_address = None contradicts Some varint.\<close>
          by (clarsimp simp: decode_address_def Let_def s_near_def s_same_def
                             word_less_nat_alt unat_eq_0
                             word_unat_eq_iff[of mode 1])
        subgoal for a aa ba \<comment> \<open>(5) pos_C.\<close>
          apply (frule varint_decode_length)
          apply (clarsimp simp: decode_address_def Let_def s_near_def s_same_def
                                word_less_nat_alt unat_eq_0
                                word_unat_eq_iff[of mode 1])
          apply (rule word_eq_sub_of_nat[where k = "length aa"])
            apply assumption
           apply simp
          apply (simp add: word_le_nat_alt)
          done
        subgoal for a aa ba \<comment> \<open>(6) addr_C.\<close>
          apply (insert cache_ok)
          apply (simp only: unat_eq_0[symmetric] word_neq_0_conv)
          by (clarsimp simp: decode_address_def Let_def s_near_def s_same_def
                             word_less_nat_alt word_unat_eq_iff[of mode 1]
                             cache_abs_def unat_sub word_le_nat_alt
                             of_nat_add word_unat.Rep_inverse
                             split: if_splits)
        subgoal \<comment> \<open>(7) unat ((np+1) mod 4) < s_near.\<close>
          by (simp add: s_near_def unat_mod)
        subgoal for a aa ba \<comment> \<open>(8) near_ptr.\<close>
          apply (clarsimp simp: decode_address_def Let_def s_near_def s_same_def
                                word_less_nat_alt cache_update_def unat_eq_0
                                word_unat_eq_iff[of mode 1])
          using cache_ok
          apply (clarsimp simp: cache_abs_def s_near_def word_less_nat_alt
                                unat_mod unat_word_ariths(1))
          done
        subgoal for a aa ba \<comment> \<open>(9) cache_abs after array writes.\<close>
          apply (insert cache_ok cache_wf_ok)
          apply (simp only: unat_eq_0[symmetric] word_neq_0_conv)
          apply (clarsimp simp: decode_address_def Let_def s_near_def s_same_def
                                word_less_nat_alt word_unat_eq_iff[of mode 1]
                                split: if_splits)
            \<comment> \<open>Derive key facts step by step.\<close>
          apply (subgoal_tac "unat (mode - 2) = unat mode - 2")
           prefer 2 apply (simp add: unat_sub word_le_nat_alt)
          apply (subgoal_tac "unat mode - 2 < s_near")
           prefer 2 apply (simp add: s_near_def)
          apply (subgoal_tac "near_arr_'' s.[unat mode - 2]
                              = word_of_nat (near c ! (unat mode - 2))")
           prefer 2 apply (simp add: cache_abs_def)
          apply (subgoal_tac "near c ! (unat mode - 2) < 2 ^ 32")
           prefer 2 apply (simp add: cache_wf_def)
          apply (subgoal_tac "unat (near_arr_'' s.[unat mode - 2]) = near c ! (unat mode - 2)")
           prefer 2 apply (simp add: unat_of_nat_eq)
          apply (subgoal_tac "unat (near_arr_'' s.[unat mode - 2] + val_C v)
                              = near c ! (unat mode - 2) + unat (val_C v)")
           prefer 2
           apply (subst unat_add_lem[THEN iffD1])
            apply simp
           apply simp
          apply (subgoal_tac "near c ! (unat mode - 2) + unat (val_C v)
                              = unat (near_arr_'' s.[unat mode - 2] + val_C v)")
           prefer 2 apply (rule sym, assumption)
          apply (erule ssubst)
          apply simp
          apply (rule cache_abs_update[OF cache_ok])
          using cache_ok apply (simp add: cache_abs_def s_near_def
                                          word_less_nat_alt)
          done
        done
      done
   (* Mode SAME (6..8): single byte index into same_arr. *)
   subgoal for x
     apply runs_to_vcg
     apply (cases "pos < addr_end")
       \<comment> \<open>pos < addr_end: read_byte' returns a valid byte.\<close>
      subgoal
        apply (rule exI[where x = "pr_t_C (pos + 1)
                                           (UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint pos)))
                                           VCD_OK"])
        apply (rule conjI)
         subgoal
           apply (subst read_byte'_spec)
            apply (rule impI)
            apply (rule buf_validD[OF buf_ok, of "unat pos", simplified uint_nat[symmetric]])
            apply (simp add: word_less_nat_alt)
           apply simp
           done
        apply runs_to_vcg
          \<comment> \<open>4 subgoals: slot < 0x300, np_in < 4, addr mod 0x300 < 0x300, post.\<close>
        subgoal \<comment> \<open>(1) slot < 0x300 via same_slot_bound.\<close>
          apply (rule same_slot_bound)
          apply (simp add: unat_eq_0[symmetric] word_neq_0_conv
                           word_less_nat_alt
                           word_unat_eq_iff[of mode 1])
          apply arith
          done
        subgoal \<comment> \<open>(2) np_in < 4.\<close>
          using cache_ok
          by (simp add: cache_abs_def s_near_def word_less_nat_alt)
        subgoal \<comment> \<open>(3) addr mod 0x300 < 0x300.\<close>
          by (simp add: word_mod_less_divisor)
        subgoal \<comment> \<open>(4) postcondition.\<close>
          apply (insert cache_ok cache_wf_ok)
          apply (subgoal_tac "unat mode \<in> {6, 7, 8}")
           prefer 2
           apply (simp add: unat_eq_0[symmetric] word_neq_0_conv
                            word_less_nat_alt
                            word_unat_eq_iff[of mode 1])
           apply arith
            \<comment> \<open>Extract head of drop.\<close>
          apply (subgoal_tac "drop (unat pos) (heap_bytes s patch (unat addr_end))
                              = heap_w8 s (patch +\<^sub>p uint pos)
                                # drop (Suc (unat pos)) (heap_bytes s patch (unat addr_end))")
           prefer 2
           apply (simp only: uint_nat)
           apply (rule heap_bytes_drop_Cons)
           apply (simp add: word_less_nat_alt)
            \<comment> \<open>Unfold decode_address.\<close>
          apply (simp add: decode_address_def Let_def s_near_def s_same_def
                           word_less_nat_alt)
            \<comment> \<open>Rewrite unat slot_w = (unat mode - 6) * 256 + unat byte.\<close>
          apply (subgoal_tac
             "unat (0xFFFFFA00 + mode * 0x100
                    + UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint pos)))
              = (unat mode - 6) * 256 + unat (heap_w8 s (patch +\<^sub>p uint pos))")
           prefer 2
           apply (rule unat_same_slot_word)
           apply fastforce
            \<comment> \<open>Using cache_abs: same_arr_'' s.[slot_n] = of_nat (same c ! slot_n).\<close>
          apply (subgoal_tac "(unat mode - 6) * 256
                              + unat (heap_w8 s (patch +\<^sub>p uint pos))
                              < same_buckets")
           prefer 2
           apply (simp add: same_buckets_def s_same_def)
           apply (subgoal_tac "unat (heap_w8 s (patch +\<^sub>p uint pos)) < 256")
            apply arith
           using unat_lt2p[of "heap_w8 s (patch +\<^sub>p uint pos)"] apply simp
          apply (subgoal_tac
             "same_arr_'' s.[(unat mode - 6) * 256
                             + unat (heap_w8 s (patch +\<^sub>p uint pos))]
              = word_of_nat (same c ! ((unat mode - 6) * 256
                                       + unat (heap_w8 s (patch +\<^sub>p uint pos))))")
           prefer 2
           apply (simp add: cache_abs_def)
            \<comment> \<open>Now simp: unat slot_w = slot_n lets same_arr_'' s.[unat slot_w] reduce.\<close>
          apply simp
          apply (rule impI)
            \<comment> \<open>Split into 3 conjuncts.\<close>
          apply (rule conjI)
           apply (simp add: unat_mod)
          apply (rule conjI)
           apply (simp add: cache_update_def s_near_def cache_abs_def unat_mod
                            unat_word_ariths(1))
            \<comment> \<open>cache_abs after array writes. Apply cache_abs_update with
                w = word_of_nat (same c ! slot_n). Use `subst` targeting the 2nd arg
                of cache_update on the conclusion.\<close>
          apply (rule subst[where P = "\<lambda>n. cache_abs _ (cache_update _ n) _",
                   of "unat ((word_of_nat :: nat \<Rightarrow> 32 word)
                              (same c ! ((unat mode - 6) * 256
                                        + unat (heap_w8 s (patch +\<^sub>p uint pos)))))"
                      "same c ! ((unat mode - 6) * 256
                                 + unat (heap_w8 s (patch +\<^sub>p uint pos)))"])
           apply (simp add: unat_of_nat_eq cache_wf_def)
          apply (rule cache_abs_update[OF cache_ok])
          using cache_ok apply (simp add: cache_abs_def s_near_def
                                          word_less_nat_alt)
          done
        done
      \<comment> \<open>pos \<ge> addr_end: read_byte' returns TRUNC. decode_address returns None
          (varint/byte-read fails). Throw VCD_ERR_TRUNC.\<close>
     subgoal
       apply (rule exI[where x = "pr_t_C pos 0 VCD_ERR_TRUNC"])
       apply (rule conjI)
        subgoal by (subst read_byte'_spec[of pos addr_end s patch]; simp)
       apply runs_to_vcg
       by (clarsimp simp: decode_address_def Let_def s_near_def s_same_def
                          word_less_nat_alt word_le_nat_alt
                          split: list.splits if_splits)
     done
  done

(* ---------- build_code_table refinement ---------- *)

(*
  Conversion from three bytes (tag/size/mode) to a half_inst. The tag
  byte matches the C's OP_* constants:
    0 = NOOP, 1 = ADD, 2 = RUN, 3 = COPY (mode in mode byte).
*)
definition byte_to_hi :: "8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> half_inst" where
  "byte_to_hi tag sz mode =
     (if tag = 0 then noop_hi
      else if tag = 1 then add_hi (unat sz)
      else if tag = 2 then run_hi (unat sz)
      else if tag = 3 then copy_hi (unat sz) (unat mode)
      else noop_hi)"

definition entry_of_row :: "(8 word, 6) array \<Rightarrow> half_inst \<times> half_inst" where
  "entry_of_row row =
     (byte_to_hi (row .[0]) (row .[1]) (row .[2]),
      byte_to_hi (row .[3]) (row .[4]) (row .[5]))"

definition code_tbl_matches :: "lifted_globals \<Rightarrow> bool" where
  "code_tbl_matches s =
     (\<forall>op < 256. entry_of_row (code_tbl_'' s .[op]) = default_entry op)"

lemma code_tbl_matches_heap_w8_update[simp]:
  "code_tbl_matches (heap_w8_update f s) = code_tbl_matches s"
  by (simp add: code_tbl_matches_def)

lemma code_tbl_matches_heap_w32_update[simp]:
  "code_tbl_matches (heap_w32_update f s) = code_tbl_matches s"
  by (simp add: code_tbl_matches_def)

lemma code_tbl_matches_near_arr_update[simp]:
  "code_tbl_matches (near_arr_''_update f s) = code_tbl_matches s"
  by (simp add: code_tbl_matches_def)

lemma code_tbl_matches_same_arr_update[simp]:
  "code_tbl_matches (same_arr_''_update f s) = code_tbl_matches s"
  by (simp add: code_tbl_matches_def)

lemma code_tbl_matches_code_tbl_built_update[simp]:
  "code_tbl_matches (code_tbl_built_''_update f s) = code_tbl_matches s"
  by (simp add: code_tbl_matches_def)

(*
  Build-code-table contract.

  Postcondition:
    - returns Result ()
    - code_tbl_built_'' s' = 1
    - code_tbl_matches s'
    - every other field is preserved (near_arr, same_arr, heap_w8,
      heap_typing, ...). For now we only state the fields we care about.
*)
(*
  Prove each whileLoop separately. Strategy: the body is deterministic
  and the counter increments by exactly 1; use runs_to_whileLoop_inc_res
  with F i = counter value at step i, S i = state at step i.

  A state description for each loop needs to say "code_tbl entries
  in range [start, start + i) match default_entry, other fields
  preserved, other code_tbl positions unchanged or still zero".
*)

\<comment> \<open>Zeroed row (all 6 slots are 0).\<close>
definition all_zero_row :: "(8 word, 6) array \<Rightarrow> bool" where
  "all_zero_row row = (\<forall>k < 6. row .[k] = 0)"

\<comment> \<open>Zero 6 slots of a row. Use `Suc 0` rather than `1` so later simp steps match.\<close>
definition zero_row :: "(8 word, 6) array \<Rightarrow> (8 word, 6) array" where
  "zero_row row = Arrays.update (Arrays.update (Arrays.update
                      (Arrays.update (Arrays.update (Arrays.update
                       row 0 0) (Suc 0) 0) 2 0) 3 0) 4 0) 5 0"

\<comment> \<open>Partial: positions [0, n) match default_entry, [n, 256) still all-zero.\<close>
definition code_tbl_matches_upto :: "lifted_globals \<Rightarrow> nat \<Rightarrow> bool" where
  "code_tbl_matches_upto s n =
     ((\<forall>op < n. entry_of_row (code_tbl_'' s .[op]) = default_entry op) \<and>
      (\<forall>op. n \<le> op \<and> op < 256 \<longrightarrow> all_zero_row (code_tbl_'' s .[op])))"

lemma code_tbl_matches_from_full_upto:
  "code_tbl_matches_upto s 256 \<Longrightarrow> code_tbl_matches s"
  by (simp add: code_tbl_matches_upto_def code_tbl_matches_def)

lemma all_zero_zero_row[simp]: "all_zero_row (zero_row row)"
proof -
  have "\<forall>k < 6. (zero_row row :: (8 word, 6) array) .[k] = 0"
  proof (intro allI impI)
    fix k :: nat
    assume "k < 6"
    then consider "k = 0" | "k = 1" | "k = 2" | "k = 3" | "k = 4" | "k = 5"
      by linarith
    thus "zero_row row .[k] = 0"
      by cases (simp_all add: zero_row_def)
  qed
  thus ?thesis by (simp add: all_zero_row_def)
qed

\<comment> \<open>Helper: after zeroing slots 0..5, the row satisfies all_zero_row.\<close>
lemma zero_all_slots:
  "all_zero_row (Arrays.update (Arrays.update (Arrays.update (Arrays.update
                    (Arrays.update (Arrays.update row 0 0) (Suc 0) 0) 2 0) 3 0) 4 0) 5 0)"
proof -
  have "\<forall>k < 6. (Arrays.update (Arrays.update (Arrays.update (Arrays.update
                    (Arrays.update (Arrays.update (row :: (8 word, 6) array) 0 0)
                     (Suc 0) 0) 2 0) 3 0) 4 0) 5 0) .[k] = 0"
  proof (intro allI impI)
    fix k :: nat
    assume "k < 6"
    then consider "k = 0" | "k = 1" | "k = 2" | "k = 3" | "k = 4" | "k = 5"
      by linarith
    thus "(Arrays.update (Arrays.update (Arrays.update (Arrays.update
            (Arrays.update (Arrays.update row 0 0) (Suc 0) 0) 2 0) 3 0) 4 0) 5 0) .[k] = 0"
      by cases simp_all
  qed
  thus ?thesis by (simp add: all_zero_row_def)
qed

\<comment> \<open>Extension lemma: matches_upto extends by one when writing 6 slots whose
    byte_to_hi decoding matches default_entry at position N.\<close>
lemma code_tbl_matches_upto_extend:
  fixes N :: nat
    and first_byte second_byte third_byte fourth_byte fifth_byte sixth_byte :: "8 word"
  assumes match: "code_tbl_matches_upto s N"
      and N_lt: "N < 256"
      and def: "default_entry N =
                  (byte_to_hi first_byte second_byte third_byte,
                   byte_to_hi fourth_byte fifth_byte sixth_byte)"
      and s'_eq: "s' = code_tbl_''_update
                        (fupdate N (\<lambda>v. Arrays.update v 5 sixth_byte) \<circ>
                         fupdate N (\<lambda>v. Arrays.update v 4 fifth_byte) \<circ>
                         fupdate N (\<lambda>v. Arrays.update v 3 fourth_byte) \<circ>
                         fupdate N (\<lambda>v. Arrays.update v 2 third_byte) \<circ>
                         fupdate N (\<lambda>v. Arrays.update v (Suc 0) second_byte) \<circ>
                         fupdate N (\<lambda>v. Arrays.update v 0 first_byte)) s"
  shows "code_tbl_matches_upto s' (Suc N)"
proof -
  have tbl_other: "\<forall>j < 256. j \<noteq> N \<longrightarrow> code_tbl_'' s' .[j] = code_tbl_'' s .[j]"
    by (clarsimp simp: s'_eq arr_fupdate_other)
  have tbl_N: "code_tbl_'' s' .[N]
               = Arrays.update (Arrays.update (Arrays.update (Arrays.update
                   (Arrays.update (Arrays.update (code_tbl_'' s .[N]) 0 first_byte)
                    (Suc 0) second_byte) 2 third_byte) 3 fourth_byte) 4 fifth_byte) 5 sixth_byte"
    using N_lt by (simp add: s'_eq arr_fupdate_same)
  have entry_N: "entry_of_row (code_tbl_'' s' .[N]) = default_entry N"
    by (simp add: tbl_N entry_of_row_def def)
  have upper: "\<forall>op. Suc N \<le> op \<and> op < 256 \<longrightarrow> all_zero_row (code_tbl_'' s' .[op])"
  proof (intro allI impI)
    fix op assume op_bd: "Suc N \<le> op \<and> op < 256"
    hence "N \<noteq> op" by auto
    hence "code_tbl_'' s' .[op] = code_tbl_'' s .[op]" using tbl_other op_bd by blast
    moreover have "all_zero_row (code_tbl_'' s .[op])"
      using match op_bd by (simp add: code_tbl_matches_upto_def)
    ultimately show "all_zero_row (code_tbl_'' s' .[op])" by simp
  qed
  have lower: "\<forall>op < Suc N. entry_of_row (code_tbl_'' s' .[op]) = default_entry op"
  proof (intro allI impI)
    fix op assume op_bd: "op < Suc N"
    show "entry_of_row (code_tbl_'' s' .[op]) = default_entry op"
    proof (cases "op = N")
      case True thus ?thesis using entry_N by simp
    next
      case False
      then have op_lt_N: "op < N" using op_bd by auto
      hence "entry_of_row (code_tbl_'' s .[op]) = default_entry op"
        using match by (simp add: code_tbl_matches_upto_def)
      moreover have "code_tbl_'' s' .[op] = code_tbl_'' s .[op]"
        using tbl_other False op_lt_N N_lt by auto
      ultimately show ?thesis by simp
    qed
  qed
  show ?thesis using upper lower by (simp add: code_tbl_matches_upto_def)
qed

lemma default_entry_add_copy_low_exact:
  assumes "mode \<le> 5" "1 \<le> add_sz" "add_sz \<le> 4" "4 \<le> copy_sz" "copy_sz \<le> 6"
  shows "default_entry (163 + mode * 12 + (add_sz - 1) * 3 + (copy_sz - 4))
       = (add_hi add_sz, copy_hi copy_sz mode)"
proof -
  let ?op = "163 + mode * 12 + (add_sz - 1) * 3 + (copy_sz - 4)"
  have add_inner: "add_sz - 1 \<le> 3" using assms by simp
  have copy_inner: "copy_sz - 4 \<le> 2" using assms by linarith
  have inner_lt: "(add_sz - 1) * 3 + (copy_sz - 4) < 12"
    using add_inner copy_inner by linarith
  have ub234: "?op \<le> 234" using assms inner_lt by linarith
  have gt162: "?op > 162" by simp
  have div_eq: "(mode * 12 + ((add_sz - 1) * 3 + (copy_sz - 4))) div 12 = mode"
    using inner_lt by simp
  have mod_eq: "(mode * 12 + ((add_sz - 1) * 3 + (copy_sz - 4))) mod 12
                 = (add_sz - 1) * 3 + (copy_sz - 4)"
    using inner_lt by simp
  have inner_div: "((add_sz - 1) * 3 + (copy_sz - 4)) div 3 = add_sz - 1"
    using copy_inner by simp
  have inner_mod: "((add_sz - 1) * 3 + (copy_sz - 4)) mod 3 = copy_sz - 4"
    using copy_inner by simp
  have add_eq: "add_sz - 1 + 1 = add_sz" using assms by simp
  have copy_eq: "copy_sz - 4 + 4 = copy_sz" using assms by simp
  have rel_eq: "?op - 163 = mode * 12 + ((add_sz - 1) * 3 + (copy_sz - 4))"
    by simp
  show ?thesis
    using ub234 gt162 div_eq mod_eq inner_div inner_mod add_eq copy_eq
    by (auto simp: default_entry_def Let_def rel_eq)
qed

lemma default_entry_add_copy_high_exact:
  assumes "6 \<le> mode" "mode \<le> 8" "1 \<le> add_sz" "add_sz \<le> 4"
  shows "default_entry (235 + (mode - 6) * 4 + (add_sz - 1))
       = (add_hi add_sz, copy_hi 4 mode)"
proof -
  let ?op = "235 + (mode - 6) * 4 + (add_sz - 1)"
  have mode_inner: "mode - 6 \<le> 2" using assms by linarith
  have add_inner: "add_sz - 1 \<le> 3" using assms by linarith
  have ub246: "?op \<le> 246" using mode_inner add_inner by linarith
  have gt234: "?op > 234" by simp
  have inner_lt: "add_sz - 1 < 4" using add_inner by simp
  have div_eq: "((mode - 6) * 4 + (add_sz - 1)) div 4 = mode - 6"
    using inner_lt by simp
  have mod_eq: "((mode - 6) * 4 + (add_sz - 1)) mod 4 = add_sz - 1"
    using inner_lt by simp
  have mode_eq: "mode - 6 + 6 = mode" using assms by simp
  have add_eq: "add_sz - 1 + 1 = add_sz" using assms by simp
  have rel_eq: "?op - 235 = (mode - 6) * 4 + (add_sz - 1)" by simp
  show ?thesis
    using ub246 gt234 div_eq mod_eq mode_eq add_eq
    by (auto simp: default_entry_def Let_def rel_eq)
qed

lemma code_tbl_matches_upto_add_copy_high_extend:
  fixes mode add_size :: "32 word"
    and N :: nat
  assumes match: "code_tbl_matches_upto s N"
      and N_eq: "N = 235 + (unat mode - 6) * 4 + (unat add_size - 1)"
      and mode_lo: "6 \<le> unat mode"
      and mode_hi: "unat mode \<le> 8"
      and add_lo: "1 \<le> unat add_size"
      and add_hi: "unat add_size \<le> 4"
  shows "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate N (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             fupdate N (\<lambda>v. Arrays.update v 4 4) \<circ>
             fupdate N (\<lambda>v. Arrays.update v 3 3) \<circ>
             fupdate N (\<lambda>v. Arrays.update v 2 0) \<circ>
             fupdate N (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
             fupdate N (\<lambda>v. Arrays.update v 0 1)) s)
          (Suc N)"
proof -
  have N_lt: "N < 256"
    using N_eq mode_lo mode_hi add_lo add_hi by linarith
  have entry: "default_entry N = (add_hi (unat add_size), copy_hi 4 (unat mode))"
  proof -
    have "default_entry (235 + (unat mode - 6) * 4 + (unat add_size - 1))
        = (add_hi (unat add_size), copy_hi 4 (unat mode))"
      by (rule default_entry_add_copy_high_exact)
         (use mode_lo mode_hi add_lo add_hi in simp_all)
    thus ?thesis using N_eq by simp
  qed
  have def: "default_entry N =
              (byte_to_hi 1 (ucast add_size) 0,
               byte_to_hi 3 4 (ucast mode))"
    using entry mode_lo mode_hi add_lo add_hi
    by (simp add: byte_to_hi_def unat_ucast)
  show ?thesis
    by (rule code_tbl_matches_upto_extend[OF match N_lt def refl])
qed

lemma code_tbl_matches_upto_add_copy_high_step:
  fixes mode add_size :: "32 word"
  assumes match: "code_tbl_matches_upto s
                    (234 + ((unat mode - 6) * 4 + unat add_size))"
      and mode_lo: "6 \<le> unat mode"
      and mode_hi: "unat mode \<le> 8"
      and add_lo: "1 \<le> unat add_size"
      and add_hi: "unat add_size \<le> 4"
  shows "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 4 4) \<circ>
             fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 3 3) \<circ>
             fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 2 0) \<circ>
             fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
             fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 0 1)) s)
          (235 + (unat mode - 6) * 4 + unat add_size)"
proof -
  let ?N = "234 + ((unat mode - 6) * 4 + unat add_size)"
  have N_eq: "?N = 235 + (unat mode - 6) * 4 + (unat add_size - 1)"
    using add_lo by simp
  have Suc_eq: "Suc ?N = 235 + (unat mode - 6) * 4 + unat add_size"
    by simp
  have step: "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate ?N (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             fupdate ?N (\<lambda>v. Arrays.update v 4 4) \<circ>
             fupdate ?N (\<lambda>v. Arrays.update v 3 3) \<circ>
             fupdate ?N (\<lambda>v. Arrays.update v 2 0) \<circ>
             fupdate ?N (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
             fupdate ?N (\<lambda>v. Arrays.update v 0 1)) s)
          (Suc ?N)"
    by (rule code_tbl_matches_upto_add_copy_high_extend
        [OF match N_eq mode_lo mode_hi add_lo add_hi])
  thus ?thesis using Suc_eq by simp
qed

lemma code_tbl_matches_upto_add_copy_high_step_nested:
  fixes mode add_size :: "32 word"
  assumes match: "code_tbl_matches_upto s
                    (234 + ((unat mode - 6) * 4 + unat add_size))"
      and mode_lo: "6 \<le> unat mode"
      and mode_hi: "unat mode \<le> 8"
      and add_lo: "1 \<le> unat add_size"
      and add_hi: "unat add_size \<le> 4"
  shows "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             (fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 4 4) \<circ>
             (fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 3 3) \<circ>
             (fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v 2 0) \<circ>
             (fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
              (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
              fupdate (234 + ((unat mode - 6) * 4 + unat add_size))
               (\<lambda>v. Arrays.update v 0 1)))))) s)
          (235 + (unat mode - 6) * 4 + unat add_size)"
  using code_tbl_matches_upto_add_copy_high_step[OF assms]
  by (simp add: o_assoc)

lemma code_tbl_matches_upto_add_copy_low_extend:
  fixes mode add_size copy_size :: "32 word"
    and N :: nat
  assumes match: "code_tbl_matches_upto s N"
      and N_eq: "N = 163 + unat mode * 12
                    + (unat add_size - 1) * 3 + (unat copy_size - 4)"
      and mode_hi: "unat mode \<le> 5"
      and add_lo: "1 \<le> unat add_size"
      and add_hi: "unat add_size \<le> 4"
      and copy_lo: "4 \<le> unat copy_size"
      and copy_hi: "unat copy_size \<le> 6"
  shows "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate N (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             fupdate N (\<lambda>v. Arrays.update v 4 (ucast copy_size)) \<circ>
             fupdate N (\<lambda>v. Arrays.update v 3 3) \<circ>
             fupdate N (\<lambda>v. Arrays.update v 2 0) \<circ>
             fupdate N (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
             fupdate N (\<lambda>v. Arrays.update v 0 1)) s)
          (Suc N)"
proof -
  have N_lt: "N < 256"
    using N_eq mode_hi add_lo add_hi copy_lo copy_hi by linarith
  have entry: "default_entry N =
                (add_hi (unat add_size), copy_hi (unat copy_size) (unat mode))"
  proof -
    have "default_entry (163 + unat mode * 12
             + (unat add_size - 1) * 3 + (unat copy_size - 4))
        = (add_hi (unat add_size), copy_hi (unat copy_size) (unat mode))"
      by (rule default_entry_add_copy_low_exact)
         (use mode_hi add_lo add_hi copy_lo copy_hi in simp_all)
    thus ?thesis using N_eq by simp
  qed
  have def: "default_entry N =
              (byte_to_hi 1 (ucast add_size) 0,
               byte_to_hi 3 (ucast copy_size) (ucast mode))"
    using entry mode_hi add_lo add_hi copy_lo copy_hi
    by (simp add: byte_to_hi_def unat_ucast)
  show ?thesis
    by (rule code_tbl_matches_upto_extend[OF match N_lt def refl])
qed

lemma code_tbl_matches_upto_add_copy_low_step_nested:
  fixes mode add_size copy_size :: "32 word"
  assumes match: "code_tbl_matches_upto s
                    (159 + (unat mode * 12
                       + ((unat add_size - 1) * 3 + unat copy_size)))"
      and mode_hi: "unat mode \<le> 5"
      and add_lo: "1 \<le> unat add_size"
      and add_hi: "unat add_size \<le> 4"
      and copy_lo: "4 \<le> unat copy_size"
      and copy_hi: "unat copy_size \<le> 6"
  shows "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 4 (ucast copy_size)) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 3 3) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 2 0) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
              fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
               (\<lambda>v. Arrays.update v 0 1)))))) s)
          (160 + (unat mode * 12
             + ((unat add_size - 1) * 3 + unat copy_size)))"
proof -
  let ?N = "159 + (unat mode * 12
                  + ((unat add_size - 1) * 3 + unat copy_size))"
  have N_eq: "?N = 163 + unat mode * 12
                    + (unat add_size - 1) * 3 + (unat copy_size - 4)"
    using copy_lo by linarith
  have Suc_eq: "Suc ?N =
                160 + (unat mode * 12
                  + ((unat add_size - 1) * 3 + unat copy_size))"
    by simp
  have step: "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate ?N (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             (fupdate ?N (\<lambda>v. Arrays.update v 4 (ucast copy_size)) \<circ>
             (fupdate ?N (\<lambda>v. Arrays.update v 3 3) \<circ>
             (fupdate ?N (\<lambda>v. Arrays.update v 2 0) \<circ>
             (fupdate ?N (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
              fupdate ?N (\<lambda>v. Arrays.update v 0 1)))))) s)
          (Suc ?N)"
    using code_tbl_matches_upto_add_copy_low_extend
      [OF match N_eq mode_hi add_lo add_hi copy_lo copy_hi]
    by (simp add: o_assoc)
  thus ?thesis using Suc_eq by simp
qed

lemma code_tbl_matches_upto_add_copy_low_step_vcg:
  fixes mode add_size copy_size :: "32 word"
  assumes match: "code_tbl_matches_upto s
                    (159 + (unat mode * 12
                       + ((unat add_size - Suc 0) * 3 + unat copy_size)))"
      and mode_hi: "unat mode \<le> 5"
      and add_lo: "1 \<le> unat add_size"
      and add_hi: "unat add_size \<le> 4"
      and copy_lo: "4 \<le> unat copy_size"
      and copy_hi: "unat copy_size \<le> 6"
  shows "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate (159 + (unat mode * 12
                + ((unat add_size - Suc 0) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - Suc 0) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 4 (ucast copy_size)) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - Suc 0) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 3 3) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - Suc 0) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 2 0) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - Suc 0) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
              fupdate (159 + (unat mode * 12
                + ((unat add_size - Suc 0) * 3 + unat copy_size)))
               (\<lambda>v. Arrays.update v 0 1)))))) s)
          (160 + (unat mode * 12
             + ((unat add_size - Suc 0) * 3 + unat copy_size)))"
proof -
  have match': "code_tbl_matches_upto s
                    (159 + (unat mode * 12
                       + ((unat add_size - 1) * 3 + unat copy_size)))"
    using match by simp
  have step: "code_tbl_matches_upto
          (code_tbl_''_update
            (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 5 (ucast mode)) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 4 (ucast copy_size)) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 3 3) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v 2 0) \<circ>
             (fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
              (\<lambda>v. Arrays.update v (Suc 0) (ucast add_size)) \<circ>
              fupdate (159 + (unat mode * 12
                + ((unat add_size - 1) * 3 + unat copy_size)))
               (\<lambda>v. Arrays.update v 0 1)))))) s)
          (160 + (unat mode * 12
             + ((unat add_size - 1) * 3 + unat copy_size)))"
    by (rule code_tbl_matches_upto_add_copy_low_step_nested
        [OF match' mode_hi add_lo add_hi copy_lo copy_hi])
  thus ?thesis by simp
qed

lemma build_code_table'_spec:
  "build_code_table' \<bullet> s
     \<lbrace> \<lambda>r s'. r = Result () \<and>
             code_tbl_built_'' s' = 1 \<and>
             code_tbl_matches s' \<and>
             near_arr_'' s' = near_arr_'' s \<and>
             same_arr_'' s' = same_arr_'' s \<rbrace>"
  unfolding build_code_table'_def
  apply runs_to_vcg
   \<comment> \<open>Loop 1: zero-init. This is a res_monad (no exceptions).\<close>
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((i :: 32 word), _). 256 - unat i)"
       and I = "\<lambda>i s'. unat i \<le> 256 \<and>
                       (\<forall>j < unat i. all_zero_row (code_tbl_'' s' .[j])) \<and>
                       near_arr_'' s' = near_arr_'' s \<and>
                       same_arr_'' s' = same_arr_'' s \<and>
                       code_tbl_built_'' s' = code_tbl_built_'' s"])
     \<comment> \<open>wf R\<close>
  subgoal by simp
     \<comment> \<open>Initial I(0, s)\<close>
  subgoal by simp
     \<comment> \<open>Exit: Loop 1 done. Apply runs_to_vcg to pull out the next whileLoop.
         After runs_to_vcg, the goal has been decomposed into obligations
         for each subsequent `modify` and each whileLoop.\<close>
  subgoal for a t
    apply clarsimp
    apply runs_to_vcg
     \<comment> \<open>Loop 2 (ADD, pos 1..18): invariant tracks matches_upto (1 + unat i).
         Precondition entering: row 0 matches default_entry 0, rows 1..255 zero.\<close>
    apply (rule runs_to_whileLoop_res'[
       where R = "measure (\<lambda>((i :: 32 word), _). 18 - unat i)"
         and I = "\<lambda>i s'. unat i \<le> 18 \<and>
                         code_tbl_matches_upto s' (1 + unat i) \<and>
                         near_arr_'' s' = near_arr_'' s \<and>
                         same_arr_'' s' = same_arr_'' s \<and>
                         code_tbl_built_'' s' = code_tbl_built_'' s"])
       \<comment> \<open>wf R\<close>
    subgoal by simp
       \<comment> \<open>Initial invariant at i=0: matches_upto (updated state) 1.\<close>
    subgoal by (simp add: code_tbl_matches_upto_def default_entry_def
                          entry_of_row_def byte_to_hi_def run_hi_def noop_hi_def
                          arr_fupdate_same arr_fupdate_other
                          word_less_nat_alt all_zero_row_def)
       \<comment> \<open>Exit Loop 2. matches_upto t' 19. Continue with Loops 3..6 + final modify.\<close>
    subgoal for a t'
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_whileLoop_res'[
         where R = "measure (\<lambda>(p, _). 9 - unat (snd (p :: 32 word \<times> 32 word)))"
           and I = "\<lambda>(idx :: 32 word, mode :: 32 word) s'.
                       unat mode \<le> 9 \<and>
                       idx = 19 + mode * 16 \<and>
                       code_tbl_matches_upto s' (19 + unat mode * 16) \<and>
                       near_arr_'' s' = near_arr_'' s \<and>
                       same_arr_'' s' = same_arr_'' s \<and>
                       code_tbl_built_'' s' = code_tbl_built_'' s"])
         \<comment> \<open>wf R\<close>
      subgoal by simp
         \<comment> \<open>Initial: I (0x13, 0) s'. matches_upto s' 19 follows from
             matches_upto t' (Suc (unat a)) and a forced to value 18 at exit.\<close>
      subgoal
        apply clarsimp
        apply (subgoal_tac "unat a = 18")
         prefer 2 apply (simp add: word_le_nat_alt word_less_nat_alt)
        apply simp
        done
         \<comment> \<open>Exit Loop 3: mode = 9. matches_upto s' 163. Continue with Loops 4..6 + final.\<close>
      subgoal for x t''
        apply (cases x, simp)
        apply clarsimp
        apply (subgoal_tac "unat b = 9")
         prefer 2 apply (simp add: word_less_nat_alt word_le_nat_alt)
        apply simp
        apply runs_to_vcg
        \<comment> \<open>Loop 4: ADD+COPY modes 0..5. Outer (idx, mode), initial (163, 0).
            Each outer iteration runs middle loop (add_size 1..4) and inner
            (copy_size 4..6). Total per mode: 4*3 = 12 entries.
            Extends matches_upto from 163+12*mode to 163+12*(mode+1). \<close>
        apply (rule runs_to_whileLoop_res'[
           where R = "measure (\<lambda>(p, _). 6 - unat (snd (p :: 32 word \<times> 32 word)))"
             and I = "\<lambda>(idx :: 32 word, mode :: 32 word) s'.
                         unat mode \<le> 6 \<and>
                         idx = 163 + mode * 12 \<and>
                         code_tbl_matches_upto s' (163 + unat mode * 12) \<and>
                         near_arr_'' s' = near_arr_'' s \<and>
                         same_arr_'' s' = same_arr_'' s \<and>
                         code_tbl_built_'' s' = code_tbl_built_'' s"])
           \<comment> \<open>wf R\<close>
        subgoal by simp
           \<comment> \<open>Initial: idx = 0x13 + 9 * 0x10 = 163 (after Loop 3 exit).\<close>
        subgoal
          apply clarsimp
          apply (rule word_unat.Rep_inject[THEN iffD1])
          apply (simp add: unat_word_ariths(2))
          done
           \<comment> \<open>Exit Loop 4 outer: mode = 6. idx = 163 + 6*12 = 235.
               Continue with Loop 5 (ADD+COPY modes 6..8, copy_size=4 fixed)
               + Loop 6 (COPY+ADD, 9 entries) + final modify. TODO.\<close>
        subgoal for x2 t2
          apply (cases t2, simp)
          apply clarsimp
          apply (subgoal_tac "unat b = 6")
           prefer 2 apply (simp add: word_less_nat_alt word_le_nat_alt)
          apply simp
          apply runs_to_vcg
          apply (rule runs_to_whileLoop_res'[
             where R = "measure (\<lambda>(p, _). 9 - unat (snd (p :: 32 word \<times> 32 word)))"
               and I = "\<lambda>(idx :: 32 word, mode :: 32 word) s'.
                           6 \<le> unat mode \<and> unat mode \<le> 9 \<and>
                           idx = 0xEB + (mode - 6) * 4 \<and>
                           code_tbl_matches_upto s' (235 + (unat mode - 6) * 4) \<and>
                           near_arr_'' s' = near_arr_'' s \<and>
                           same_arr_'' s' = same_arr_'' s \<and>
                           code_tbl_built_'' s' = code_tbl_built_'' s"])
          subgoal by simp
          subgoal
            apply clarsimp
            apply (rule word_unat.Rep_inject[THEN iffD1])
            apply (simp add: unat_word_ariths(1) unat_word_ariths(2))
            done
          subgoal for xh th
            apply (cases th, simp)
            apply (subgoal_tac "unat b = 9")
             prefer 2 apply (simp add: word_less_nat_alt word_le_nat_alt)
            apply simp
            apply runs_to_vcg
            apply (rule runs_to_whileLoop_res'[
               where R = "measure (\<lambda>(p, _). 9 - unat (snd (p :: 32 word \<times> 32 word)))"
                 and I = "\<lambda>(idx :: 32 word, mode :: 32 word) s'.
                             unat mode \<le> 9 \<and>
                             idx = 247 + mode \<and>
                             code_tbl_matches_upto s' (247 + unat mode) \<and>
                             near_arr_'' s' = near_arr_'' s \<and>
                             same_arr_'' s' = same_arr_'' s \<and>
                             code_tbl_built_'' s' = code_tbl_built_'' s"])
            subgoal by simp
            subgoal
              apply clarsimp
              apply (rule word_unat.Rep_inject[THEN iffD1])
              apply (simp add: unat_word_ariths(1) unat_word_ariths(2))
              done
            subgoal for xc tc
              apply (cases tc, simp)
              apply (subgoal_tac "unat b = 9")
               prefer 2 apply (simp add: word_less_nat_alt word_le_nat_alt)
              apply simp
              apply runs_to_vcg
              apply (rule code_tbl_matches_from_full_upto)
              apply (simp add: code_tbl_matches_upto_def)
              done
            subgoal for xc tc
              apply (cases tc, simp)
              apply runs_to_vcg
              subgoal for copy_mode
                by (simp add: word_less_nat_alt unat_word_ariths(1))
              subgoal for copy_mode
                apply (subgoal_tac "unat copy_mode < 9")
                 prefer 2 apply (simp add: word_less_nat_alt)
                by (simp add: unat_word_ariths(1) word_less_nat_alt)
              subgoal for copy_mode
                apply (subgoal_tac "unat copy_mode < 9")
                 prefer 2 apply (simp add: word_less_nat_alt)
                apply (subgoal_tac "unat (copy_mode + 1) = unat copy_mode + 1")
                 prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
                apply (subgoal_tac "unat (0xF7 + copy_mode) = 247 + unat copy_mode")
                 prefer 2 apply (simp add: unat_word_ariths(1))
                apply (simp add: code_tbl_matches_upto_def)
                apply (intro conjI allI impI)
                subgoal for op
                  apply (cases "op = 247 + unat copy_mode")
                   subgoal
                     apply simp
                     apply (simp add: arr_fupdate_same arr_fupdate_other
                                      entry_of_row_def byte_to_hi_def
                                      copy_hi_def add_hi_def default_entry_copy_add
                                      unat_ucast)
                     done
                  subgoal
                    apply (simp add: arr_fupdate_other)
                    done
                  done
                subgoal for op
                  by (simp add: arr_fupdate_other)
                done
              subgoal for copy_mode
                apply (subgoal_tac "unat copy_mode < 9")
                 prefer 2 apply (simp add: word_less_nat_alt)
                by (simp add: unat_word_ariths(1) word_less_nat_alt)
  done
  done
          subgoal premises high_prems for outer_mode high_pair high_state
          proof (cases high_pair)
            case (Pair idx mode)
            have mode_lt9: "unat mode < 9"
              using high_prems Pair by (simp add: word_less_nat_alt)
            have mode_bounds: "6 \<le> unat mode" "unat mode \<le> 8"
              using high_prems Pair mode_lt9 by simp_all
            show ?thesis
              using high_prems Pair
              apply simp
              apply runs_to_vcg
              apply (rule runs_to_whileLoop_res'[
                 where R = "measure (\<lambda>(p, _). 5 - unat (fst (p :: 32 word \<times> 32 word)))"
                   and I = "\<lambda>(add_size :: 32 word, idx' :: 32 word) s'.
                               1 \<le> unat add_size \<and> unat add_size \<le> 5 \<and>
                               idx' = 0xEB + (mode - 6) * 4 + (add_size - 1) \<and>
                               code_tbl_matches_upto s'
                                 (235 + (unat mode - 6) * 4 + (unat add_size - 1)) \<and>
                               near_arr_'' s' = near_arr_'' s \<and>
                               same_arr_'' s' = same_arr_'' s \<and>
                               code_tbl_built_'' s' = code_tbl_built_'' s"])
              subgoal by simp
              subgoal by simp
              subgoal for xi ti
                apply (cases xi, simp)
                apply runs_to_vcg
                subgoal for add_size
                  using mode_lt9 mode_bounds
                  apply clarsimp
                  apply (subgoal_tac "unat add_size = 5")
                   prefer 2 apply (simp add: word_less_nat_alt word_le_nat_alt)
                  apply (subgoal_tac "unat (mode + 1) = unat mode + 1")
                   prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
                  apply (intro conjI)
                      subgoal by simp
                     subgoal by simp
                    subgoal
                      apply (rule word_unat.Rep_inject[THEN iffD1])
                      apply (simp add: unat_word_ariths(1) unat_word_ariths(2))
                      done
                   subgoal
                     apply (subgoal_tac
                       "239 + (unat mode - 6) * 4 = 235 + (unat mode - 5) * 4")
                      apply simp
                     using mode_bounds apply linarith
                     done
                  subgoal by (simp add: word_less_nat_alt unat_word_ariths(1))
                  done
                done
              subgoal for xi ti
                apply (cases xi, simp)
                apply runs_to_vcg
                subgoal for add_size
                  using mode_lt9 mode_bounds
                  apply (subgoal_tac "unat add_size < 5")
                   prefer 2 apply (simp add: word_less_nat_alt)
                  by (simp add: word_less_nat_alt unat_word_ariths(1) unat_word_ariths(2))
                subgoal for add_size
                  apply (subgoal_tac "unat add_size < 5")
                   prefer 2 apply (simp add: word_less_nat_alt)
                  by (simp add: unat_word_ariths(1) word_less_nat_alt)
                subgoal for add_size
                  apply (subgoal_tac "unat add_size < 5")
                   prefer 2 apply (simp add: word_less_nat_alt)
                  by (simp add: unat_word_ariths(1) word_less_nat_alt)
                subgoal for add_size
                  using mode_lt9 mode_bounds
                  apply (subgoal_tac "unat add_size < 5")
                   prefer 2 apply (simp add: word_less_nat_alt)
                  apply (subgoal_tac "unat (add_size + 1) = unat add_size + 1")
                   prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
                  apply (subgoal_tac
                    "unat (0xD2 + (mode * 4 + add_size)) =
                       235 + (unat mode - 6) * 4 + (unat add_size - 1)")
                   prefer 2 apply (simp add: unat_word_ariths(1) unat_word_ariths(2))
                  apply simp
                  apply (rule code_tbl_matches_upto_add_copy_high_step_nested)
                      apply simp
                     apply simp
                    apply simp
                   apply simp
                  apply simp
                  done
                subgoal for add_size
                  apply (subgoal_tac "unat add_size < 5")
                   prefer 2 apply (simp add: word_less_nat_alt)
                  by (simp add: unat_word_ariths(1) word_less_nat_alt)
                done
              done
          qed
  done
        subgoal premises low_prems for loop3_mode low_pair low_state
        proof (cases low_pair)
          case (Pair idx mode)
          have mode_lt6: "unat mode < 6"
            using low_prems Pair by (simp add: word_less_nat_alt)
          have mode_le5: "unat mode \<le> 5"
            using mode_lt6 by simp
          show ?thesis
            using low_prems Pair
            apply simp
            apply runs_to_vcg
            apply (rule runs_to_whileLoop_res'[
               where R = "measure (\<lambda>(p, _). 5 - unat (fst (p :: 32 word \<times> 32 word)))"
                 and I = "\<lambda>(add_size :: 32 word, idx' :: 32 word) s'.
                             1 \<le> unat add_size \<and> unat add_size \<le> 5 \<and>
                             idx' = 0xA3 + mode * 0xC + (add_size - 1) * 3 \<and>
                             code_tbl_matches_upto s'
                               (163 + unat mode * 12 + (unat add_size - 1) * 3) \<and>
                             near_arr_'' s' = near_arr_'' s \<and>
                             same_arr_'' s' = same_arr_'' s \<and>
                             code_tbl_built_'' s' = code_tbl_built_'' s"])
            subgoal by simp
            subgoal by simp
            subgoal for xi ti
              apply (cases xi, simp)
              apply runs_to_vcg
              subgoal for add_size
                using mode_lt6 mode_le5
                apply clarsimp
                apply (subgoal_tac "unat add_size = 5")
                 prefer 2 apply (simp add: word_less_nat_alt word_le_nat_alt)
                apply (subgoal_tac "unat (mode + 1) = unat mode + 1")
                 prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
                apply (intro conjI)
                    subgoal by simp
                   subgoal
                     apply (rule word_unat.Rep_inject[THEN iffD1])
                     apply (simp add: unat_word_ariths(1) unat_word_ariths(2))
                     done
                  subgoal
                    apply (subgoal_tac "163 + (unat mode + 1) * 12 =
                                        175 + unat mode * 12")
                     apply simp
                    apply simp
                    done
                 subgoal by simp
                done
              done
            subgoal for xi ti
              apply (cases xi, simp)
              apply runs_to_vcg
              apply (rule runs_to_whileLoop_res'[
                 where R = "measure (\<lambda>(p, _). 7 - unat (fst (p :: 32 word \<times> 32 word)))"
                   and I = "\<lambda>(copy_size :: 32 word, idx' :: 32 word) s'.
                               4 \<le> unat copy_size \<and> unat copy_size \<le> 7 \<and>
                               idx' = 0xA3 + mode * 0xC + (fst xi - 1) * 3
                                      + (copy_size - 4) \<and>
                               code_tbl_matches_upto s'
                                 (163 + unat mode * 12 + (unat (fst xi) - 1) * 3
                                      + (unat copy_size - 4)) \<and>
                               near_arr_'' s' = near_arr_'' s \<and>
                               same_arr_'' s' = same_arr_'' s \<and>
                               code_tbl_built_'' s' = code_tbl_built_'' s"])
              subgoal by simp
              subgoal by simp
              subgoal for xci tci
                apply (cases tci, simp)
                apply runs_to_vcg
                subgoal
                  apply clarsimp
                  apply (subgoal_tac "unat (fst xi) < 5")
                   prefer 2 apply (simp add: word_less_nat_alt)
                  apply (subgoal_tac "unat (fst xi + 1) = unat (fst xi) + 1")
                   prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
                  apply (subgoal_tac "unat (fst tci) = 7")
                   prefer 2 apply (simp add: word_le_nat_alt word_less_nat_alt)
                  apply (intro conjI)
                      subgoal by simp
                     subgoal by simp
                    subgoal
                      apply (rule word_unat.Rep_inject[THEN iffD1])
                      apply (simp add: unat_word_ariths(1) unat_word_ariths(2))
                      done
                   subgoal
                     apply (subgoal_tac
                       "163 + unat mode * 12 + (unat (fst xi) + 1 - Suc 0) * 3
                        = 159 + (unat mode * 12
                           + ((unat (fst xi) - Suc 0) * 3 + 7))")
                      apply simp
                     apply simp
                     done
                  subgoal by (simp add: word_less_nat_alt)
                  done
                done
              subgoal premises copy_prems for xci tci
              proof (cases tci)
                case (Pair copy_size copy_idx)
                show ?thesis
                  using copy_prems Pair mode_le5
                  apply simp
                  apply runs_to_vcg
                  subgoal
                    apply (subgoal_tac "unat (fst xi) < 5")
                     prefer 2 apply (simp add: word_less_nat_alt)
                    apply (subgoal_tac "unat copy_size < 7")
                     prefer 2 apply (simp add: word_less_nat_alt)
                    by (simp add: word_less_nat_alt unat_word_ariths(1) unat_word_ariths(2))
                  subgoal
                    apply (subgoal_tac "unat copy_size < 7")
                     prefer 2 apply (simp add: word_less_nat_alt)
                    by (simp add: unat_word_ariths(1) word_less_nat_alt)
                  subgoal
                    apply (subgoal_tac "unat copy_size < 7")
                     prefer 2 apply (simp add: word_less_nat_alt)
                    by (simp add: unat_word_ariths(1) word_less_nat_alt)
                  subgoal
                    apply (subgoal_tac "unat (fst xi) < 5")
                     prefer 2 apply (simp add: word_less_nat_alt)
                    apply (subgoal_tac "unat copy_size < 7")
                     prefer 2 apply (simp add: word_less_nat_alt)
                    apply (subgoal_tac "unat (copy_size + 1) = unat copy_size + 1")
                     prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
                    apply (subgoal_tac
                      "unat (0x9F + (mode * 0xC + ((fst xi - 1) * 3 + copy_size))) =
                         159 + (unat mode * 12
                           + ((unat (fst xi) - 1) * 3 + unat copy_size))")
                     prefer 2 apply (simp add: unat_word_ariths(1) unat_word_ariths(2))
                    apply simp
                    apply (rule code_tbl_matches_upto_add_copy_low_step_vcg
                      [where mode=mode and add_size=xci and copy_size=copy_size])
                         apply simp
                        apply simp
                       apply simp
                      apply simp
                     apply simp
                    apply simp
                    done
                  subgoal
                    apply (subgoal_tac "unat copy_size < 7")
                     prefer 2 apply (simp add: word_less_nat_alt)
                    by (simp add: unat_word_ariths(1) word_less_nat_alt)
                  done
              qed
              done
            done
        qed
  done
         \<comment> \<open>Body Loop 3 (outer). First writes the size-0 entry at idx = 19+mode*16,
             then runs the inner size-loop for sizes 4..18.\<close>
      subgoal for x t''
        apply clarsimp
        apply runs_to_vcg
        subgoal for y
          apply (subgoal_tac "unat y < 9")
           prefer 2 apply (simp add: word_less_nat_alt)
          apply (simp add: word_less_nat_alt unat_word_ariths(1)
                           unat_word_ariths(2))
          done
        subgoal for y
          apply (rule runs_to_whileLoop_res'[
             where R = "measure (\<lambda>(p, _). 19 - unat (snd (p :: 32 word \<times> 32 word)))"
               and I = "\<lambda>(idx :: 32 word, size :: 32 word) s'.
                           4 \<le> unat size \<and> unat size \<le> 19 \<and>
                           idx = (20 + y * 16) + (size - 4) \<and>
                           code_tbl_matches_upto s' (20 + unat y * 16 + (unat size - 4)) \<and>
                           near_arr_'' s' = near_arr_'' s \<and>
                           same_arr_'' s' = same_arr_'' s \<and>
                           code_tbl_built_'' s' = code_tbl_built_'' s"])
          subgoal by simp
          subgoal
            apply clarsimp
            apply (subgoal_tac "unat y \<le> 8")
             prefer 2 apply (simp add: word_less_nat_alt)
            apply (subgoal_tac "unat (0x13 + y * 0x10) = 19 + unat y * 16")
             prefer 2 apply (simp add: word_less_nat_alt unat_word_ariths(1)
                                       unat_word_ariths(2))
            apply (subgoal_tac "19 + unat y * 16 < CARD(256)")
             prefer 2 apply simp
            apply (simp add: code_tbl_matches_upto_def)
            apply (intro conjI allI impI)
            subgoal for op
              apply (cases "op = 19 + unat y * 16")
               subgoal
                 apply simp
                 apply (subgoal_tac "all_zero_row (code_tbl_'' t'' .[19 + unat y * 16])")
                  prefer 2
                  apply (simp add: code_tbl_matches_upto_def)
                  apply (drule conjunct2, drule_tac x = "19 + unat y * 16" in spec)
                  apply simp
                 apply (simp add: arr_fupdate_same arr_fupdate_other
                                  default_entry_copy_varint
                                  entry_of_row_def byte_to_hi_def
                                  copy_hi_def noop_hi_def unat_ucast
                                  all_zero_row_def)
                 done
              subgoal
                apply (simp add: arr_fupdate_other code_tbl_matches_upto_def)
                done
              done
            subgoal for op
              by (simp add: arr_fupdate_other code_tbl_matches_upto_def)
            done
          subgoal for x t'''
            apply (cases x, simp)
            apply runs_to_vcg
            apply clarsimp
            apply (subgoal_tac "unat y < 9")
             prefer 2 apply (simp add: word_less_nat_alt)
            apply (subgoal_tac "unat (y + 1) = unat y + 1")
             prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
            apply (subgoal_tac "unat b = 19")
             prefer 2 apply (simp add: word_le_nat_alt word_less_nat_alt)
            apply (intro conjI)
               subgoal by simp
              subgoal
                apply (subst word_unat_eq_iff)
                apply simp
                done
             subgoal by clarsimp
            subgoal by (simp add: word_less_nat_alt)
            done
          subgoal for x t'''
            apply clarsimp
            apply runs_to_vcg
            subgoal for ya
              apply (subgoal_tac "unat ya \<le> 18 \<and> unat y \<le> 8")
               prefer 2 apply (simp add: word_less_nat_alt)
              by (simp add: word_less_nat_alt unat_word_ariths(1) unat_word_ariths(2))
            subgoal for ya
              apply (subgoal_tac "unat ya < 19")
               prefer 2 apply (simp add: word_less_nat_alt)
              by (simp add: unat_word_ariths(1) word_less_nat_alt)
            subgoal for ya
              apply (subgoal_tac "unat ya < 19")
               prefer 2 apply (simp add: word_less_nat_alt)
              by (simp add: unat_word_ariths(1) word_less_nat_alt)
            subgoal for ya
              apply (subgoal_tac "unat ya \<le> 18 \<and> 4 \<le> unat ya \<and> unat y \<le> 8")
               prefer 2 apply (simp add: word_less_nat_alt)
              apply (subgoal_tac "unat (0x10 + (y * 0x10 + ya)) = 16 + unat y * 16 + unat ya")
               prefer 2 apply (simp add: word_less_nat_alt unat_word_ariths(1)
                                         unat_word_ariths(2))
              apply (subgoal_tac "16 + unat y * 16 + unat ya < CARD(256)")
               prefer 2 apply simp
              apply (subgoal_tac "unat (ya + 1) = unat ya + 1")
               prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
              apply (simp add: code_tbl_matches_upto_def)
              apply (intro conjI allI impI)
              subgoal for op
                apply (cases "op = 16 + unat y * 16 + unat ya")
                 subgoal
                   apply simp
                   apply (subgoal_tac "all_zero_row (code_tbl_'' t''' .[16 + unat y * 16 + unat ya])")
                    prefer 2
                    apply (drule conjunct2, drule_tac x = "16 + unat y * 16 + unat ya" in spec)
                    apply simp
                   apply (subgoal_tac "default_entry (16 + unat y * 16 + unat ya)
                                       = (copy_hi (unat ya) (unat y), noop_hi)")
                    prefer 2
                    apply (subgoal_tac "16 + unat y * 16 + unat ya
                                        = 19 + unat y * 16 + unat ya - 3")
                     prefer 2 apply simp
                    apply (simp only: default_entry_copy_small)
                   apply (simp add: arr_fupdate_same arr_fupdate_other
                                    entry_of_row_def byte_to_hi_def
                                    copy_hi_def noop_hi_def unat_ucast
                                    all_zero_row_def)
                   done
                subgoal
                  by (simp add: arr_fupdate_other)
                done
              subgoal for op
                by (simp add: arr_fupdate_other)
              done
            subgoal for ya
              apply (subgoal_tac "unat ya < 19")
               prefer 2 apply (simp add: word_less_nat_alt)
              by (simp add: unat_word_ariths(1) word_less_nat_alt)
            done
          done
        done
      done
       \<comment> \<open>Body step for Loop 2.\<close>
    subgoal for a t'
      apply clarsimp
      apply runs_to_vcg
      subgoal
        by (simp add: word_less_nat_alt unat_word_ariths(1))
      subgoal
        by (simp add: word_less_nat_alt unat_word_ariths(1))
      subgoal
        apply (subgoal_tac "unat (a + 1) = unat a + 1")
         prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
        apply (subgoal_tac "unat (1 + a) = 1 + unat a")
         prefer 2 apply (simp add: unat_word_ariths(1) word_less_nat_alt)
        apply (subgoal_tac "1 + unat a < CARD(256)")
         prefer 2 apply (simp add: word_less_nat_alt)
        apply (simp add: code_tbl_matches_upto_def)
        apply (intro conjI allI impI)
        subgoal for op
          apply (cases "op = 1 + unat a")
           subgoal
             apply simp
             apply (simp add: arr_fupdate_same arr_fupdate_other)
             apply (subgoal_tac "all_zero_row (code_tbl_'' t' .[Suc (unat a)])")
              prefer 2
              apply (drule conjunct2, drule_tac x = "Suc (unat a)" in spec)
              apply simp
             apply (cases "unat a = 0")
              subgoal
                by (simp add: default_entry_def entry_of_row_def byte_to_hi_def
                              add_hi_def noop_hi_def unat_ucast all_zero_row_def)
             subgoal
               apply (subgoal_tac "1 \<le> unat a \<and> unat a \<le> 17")
                prefer 2 apply (simp add: word_less_nat_alt)
               apply (subgoal_tac "default_entry (Suc (unat a)) = (add_hi (unat a), noop_hi)")
                prefer 2 apply (metis Suc_eq_plus1_left default_entry_add_small)
               apply (simp add: entry_of_row_def byte_to_hi_def
                                add_hi_def noop_hi_def unat_ucast
                                all_zero_row_def)
               done
             done
          subgoal
            apply (simp add: arr_fupdate_other)
            done
          done
        subgoal for op
          by (simp add: arr_fupdate_other)
        done
      subgoal
        by (simp add: word_less_nat_alt unat_word_ariths(1))
      done
    done
     \<comment> \<open>Body step: zero-initialise the current row and advance the index.\<close>
  subgoal for a t
    apply runs_to_vcg
    subgoal by (simp add: word_less_nat_alt unat_word_ariths(1))
    subgoal premises prems for j
    proof (cases "j < unat a")
      case True
      have j_lt: "j < CARD(256)" using True prems by (simp add: word_less_nat_alt)
      have "fupdate (unat a) (\<lambda>v. Arrays.update v 5 0)
             (fupdate (unat a) (\<lambda>v. Arrays.update v 4 0)
              (fupdate (unat a) (\<lambda>v. Arrays.update v 3 0)
               (fupdate (unat a) (\<lambda>v. Arrays.update v 2 0)
                (fupdate (unat a) (\<lambda>v. Arrays.update v (Suc 0) 0)
                 (fupdate (unat a) (\<lambda>v. Arrays.update v 0 0)
                  (code_tbl_'' t)))))) .[j]
           = code_tbl_'' t .[j]"
        using True j_lt by (simp add: arr_fupdate_other)
      thus ?thesis using prems True by simp
    next
      case False
      have unat_a1: "unat (a + 1) = unat a + 1"
        using prems by (simp add: unat_word_ariths(1) word_less_nat_alt)
      have j_eq: "j = unat a" using False prems unat_a1 by simp
      have unat_a_lt: "unat a < 256" using prems by (simp add: word_less_nat_alt)
      have row_eq: "fupdate (unat a) (\<lambda>v. Arrays.update v 5 0)
                     (fupdate (unat a) (\<lambda>v. Arrays.update v 4 0)
                      (fupdate (unat a) (\<lambda>v. Arrays.update v 3 0)
                       (fupdate (unat a) (\<lambda>v. Arrays.update v 2 0)
                        (fupdate (unat a) (\<lambda>v. Arrays.update v (Suc 0) 0)
                         (fupdate (unat a) (\<lambda>v. Arrays.update v 0 0)
                          (code_tbl_'' t)))))) .[unat a]
                   = Arrays.update (Arrays.update (Arrays.update (Arrays.update
                      (Arrays.update (Arrays.update (code_tbl_'' t .[unat a])
                       0 0) (Suc 0) 0) 2 0) 3 0) 4 0) 5 0"
        using unat_a_lt by (simp add: arr_fupdate_same)
      have "all_zero_row (fupdate (unat a) (\<lambda>v. Arrays.update v 5 0)
                           (fupdate (unat a) (\<lambda>v. Arrays.update v 4 0)
                            (fupdate (unat a) (\<lambda>v. Arrays.update v 3 0)
                             (fupdate (unat a) (\<lambda>v. Arrays.update v 2 0)
                              (fupdate (unat a) (\<lambda>v. Arrays.update v (Suc 0) 0)
                               (fupdate (unat a) (\<lambda>v. Arrays.update v 0 0)
                                (code_tbl_'' t))))))
                           .[unat a])"
        using row_eq zero_all_slots by simp
      thus ?thesis using j_eq by simp
    qed
    subgoal by (simp add: word_less_nat_alt unat_word_ariths(1))
    done
  done


(*
  Stronger variant of build_code_table'_spec used downstream: also
  states that heap_typing is preserved.  (build_code_table' only
  modifies code_tbl_'' and code_tbl_built_'', neither of which
  affects heap_typing.)
*)
lemma build_code_table'_heap_typing:
  "build_code_table' \<bullet> s
     \<lbrace> \<lambda>_ s'. heap_typing s' = heap_typing s \<rbrace>"
proof -
  have ut: "build_code_table' \<bullet> s
      ?\<lbrace> \<lambda>_ s'. unchanged_typing_on UNIV s s' \<rbrace>"
    by (rule unchanged_typing)
  have partial: "build_code_table' \<bullet> s
      ?\<lbrace> \<lambda>_ s'. heap_typing s' = heap_typing s \<rbrace>"
    apply (rule runs_to_partial_weaken[OF ut])
    apply (simp add: unchanged_typing_on_UNIV_iff)
    done
  show ?thesis
    by (rule runs_to_of_runs_to_partial_runs_to'[OF build_code_table'_spec partial])
qed

lemma build_code_table'_preserves_typing:
  "build_code_table' \<bullet> s
     \<lbrace> \<lambda>r s'. r = Result () \<and>
             code_tbl_built_'' s' = 1 \<and>
             code_tbl_matches s' \<and>
             near_arr_'' s' = near_arr_'' s \<and>
             same_arr_'' s' = same_arr_'' s \<and>
             heap_typing s' = heap_typing s \<rbrace>"
  using build_code_table'_spec[of s] build_code_table'_heap_typing[of s]
  by (simp add: runs_to_conj)

lemma build_code_table'_setup_partial:
  "build_code_table' \<bullet> s
     ?\<lbrace> \<lambda>_ s'. heap_typing s' = heap_typing s \<and>
             heap_bytes s' patch patch_n = heap_bytes s patch patch_n \<and>
             heap_bytes s' src src_n = heap_bytes s src src_n \<and>
             heap_w32 s' out_len = heap_w32 s out_len \<rbrace>"
  unfolding build_code_table'_def
  supply whileLoop_preserves_partial
    [where P = "\<lambda>s'. heap_typing s' = heap_typing s \<and>
                       heap_bytes s' patch patch_n = heap_bytes s patch patch_n \<and>
                       heap_bytes s' src src_n = heap_bytes s src src_n \<and>
                       heap_w32 s' out_len = heap_w32 s out_len",
     runs_to_vcg]
  by runs_to_vcg

lemma build_code_table'_setup:
  "build_code_table' \<bullet> s
    \<lbrace>\<lambda>r s'. r = Result () \<and>
            code_tbl_built_'' s' = 1 \<and>
            code_tbl_matches s' \<and>
            near_arr_'' s' = near_arr_'' s \<and>
            same_arr_'' s' = same_arr_'' s \<and>
            heap_typing s' = heap_typing s \<and>
            heap_bytes s' patch patch_n = heap_bytes s patch patch_n \<and>
            heap_bytes s' src src_n = heap_bytes s src src_n \<and>
            heap_w32 s' out_len = heap_w32 s out_len\<rbrace>"
proof -
  have partial: "build_code_table' \<bullet> s
     ?\<lbrace> \<lambda>_ s'. heap_typing s' = heap_typing s \<and>
             heap_bytes s' patch patch_n = heap_bytes s patch patch_n \<and>
             heap_bytes s' src src_n = heap_bytes s src src_n \<and>
             heap_w32 s' out_len = heap_w32 s out_len \<rbrace>"
    by (rule build_code_table'_setup_partial)
  have total: "build_code_table' \<bullet> s
     \<lbrace> \<lambda>_ s'. heap_typing s' = heap_typing s \<and>
             heap_bytes s' patch patch_n = heap_bytes s patch patch_n \<and>
             heap_bytes s' src src_n = heap_bytes s src src_n \<and>
             heap_w32 s' out_len = heap_w32 s out_len \<rbrace>"
    by (rule runs_to_of_runs_to_partial_runs_to'[OF build_code_table'_spec partial])
  show ?thesis
    using build_code_table'_spec[of s] total
    by (simp add: runs_to_conj)
qed


lemma vcdiff_decode'_short_patch:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and short_patch: "patch_len < 5"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (-1) \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
  unfolding vcdiff_decode'_def
  apply runs_to_vcg
  using out_len_ok short_patch
  apply (auto simp: word_less_nat_alt)
  done

lemma vcdiff_decode'_magic0_fail:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 1"
      and len_ok: "5 \<le> patch_len"
      and bad_magic0: "uint (heap_w8 s patch) \<noteq> 214"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (-2) \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
  unfolding vcdiff_decode'_def
  apply runs_to_vcg
  using out_len_ok patch_ok len_ok bad_magic0
  apply (auto simp: buf_valid_def word_less_nat_alt word_le_nat_alt)
  done

lemma vcdiff_decode'_magic1_fail:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 2"
      and len_ok: "5 \<le> patch_len"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and bad_magic1: "uint (heap_w8 s (patch +\<^sub>p 1)) \<noteq> 195"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (-2) \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok len_ok magic0_ok bad_magic1 patch0_ok patch1_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    done
qed

lemma vcdiff_decode'_magic2_fail:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 3"
      and len_ok: "5 \<le> patch_len"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and bad_magic2: "uint (heap_w8 s (patch +\<^sub>p 2)) \<noteq> 196"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (-2) \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok len_ok magic0_ok magic1_ok bad_magic2 patch0_ok patch1_ok patch2_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    done
qed

lemma vcdiff_decode'_magic3_fail:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 4"
      and len_ok: "5 \<le> patch_len"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and bad_magic3: "uint (heap_w8 s (patch +\<^sub>p 3)) \<noteq> 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (-2) \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok len_ok magic0_ok magic1_ok magic2_ok bad_magic3
          patch0_ok patch1_ok patch2_ok patch3_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    done
qed

lemma vcdiff_decode'_hdr_fail:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 5"
      and len_ok: "5 \<le> patch_len"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and magic3_ok: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
      and bad_hdr: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 \<noteq> 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (-3) \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] by simp
  have patch4_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 4)"
    using buf_validD[OF patch_ok, of 4] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok len_ok magic0_ok magic1_ok magic2_ok magic3_ok bad_hdr
          patch0_ok patch1_ok patch2_ok patch3_ok patch4_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    done
qed

lemma vcdiff_decode'_appheader_len5_nonok:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 5"
      and len_eq: "patch_len = 5"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and magic3_ok: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
      and hdr_ok: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 = 0"
      and app_set: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 4 \<noteq> 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] by simp
  have patch4_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 4)"
    using buf_validD[OF patch_ok, of 4] by simp
  have buf_upd: "buf_valid (heap_w32_update (\<lambda>h. h(out_len := 0)) s) patch 5"
    using patch_ok by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok len_eq magic0_ok magic1_ok magic2_ok magic3_ok hdr_ok app_set
          patch0_ok patch1_ok patch2_ok patch3_ok patch4_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    subgoal
      apply (rule runs_to_weaken[
        OF read_varint'_at_end_nonok
         [where s = "heap_w32_update (\<lambda>h. h(out_len := 0)) s" and buf = patch and len = 5]])
      subgoal using buf_upd by simp
      apply (clarsimp simp: len_eq)
      done
    done
qed

lemma vcdiff_decode'_short_nonok:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and short_patch: "patch_len < 5"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
  apply (rule runs_to_weaken[OF vcdiff_decode'_short_patch[OF out_len_ok short_patch]])
  by simp

lemma vcdiff_decode'_magic0_nonok:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 1"
      and len_ok: "5 \<le> patch_len"
      and bad_magic0: "uint (heap_w8 s patch) \<noteq> 214"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
  apply (rule runs_to_weaken[OF vcdiff_decode'_magic0_fail[OF out_len_ok patch_ok len_ok bad_magic0]])
  by simp

lemma vcdiff_decode'_magic1_nonok:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 2"
      and len_ok: "5 \<le> patch_len"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and bad_magic1: "uint (heap_w8 s (patch +\<^sub>p 1)) \<noteq> 195"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
  apply (rule runs_to_weaken[
    OF vcdiff_decode'_magic1_fail[OF out_len_ok patch_ok len_ok magic0_ok bad_magic1]])
  by simp

lemma vcdiff_decode'_magic2_nonok:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 3"
      and len_ok: "5 \<le> patch_len"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and bad_magic2: "uint (heap_w8 s (patch +\<^sub>p 2)) \<noteq> 196"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
  apply (rule runs_to_weaken[
    OF vcdiff_decode'_magic2_fail[OF out_len_ok patch_ok len_ok magic0_ok magic1_ok bad_magic2]])
  by simp

lemma vcdiff_decode'_magic3_nonok:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 4"
      and len_ok: "5 \<le> patch_len"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and bad_magic3: "uint (heap_w8 s (patch +\<^sub>p 3)) \<noteq> 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
  apply (rule runs_to_weaken[
    OF vcdiff_decode'_magic3_fail[OF out_len_ok patch_ok len_ok magic0_ok magic1_ok magic2_ok bad_magic3]])
  by simp

lemma vcdiff_decode'_hdr_nonok:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 5"
      and len_ok: "5 \<le> patch_len"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and magic3_ok: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
      and bad_hdr: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 \<noteq> 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
  apply (rule runs_to_weaken[
    OF vcdiff_decode'_hdr_fail[OF out_len_ok patch_ok len_ok magic0_ok magic1_ok magic2_ok magic3_ok bad_hdr]])
  by simp

lemma near_init_loop_res_w32:
  "(whileLoop (\<lambda>idx st. unat idx < 4)
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word) \<and> heap_w32 t p = heap_w32 s0 p \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 4 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 4 \<and> heap_w32 st p = heap_w32 s0 p"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (clarsimp simp: word_less_nat_alt)
    apply (cases "unat idx")
     apply (auto simp: unat_word_ariths(1) word_less_nat_alt)
    done
  done

lemma same_init_loop_res_w32:
  "(whileLoop (\<lambda>idx st. unat idx < 768)
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (768 :: 32 word) \<and> heap_w32 t p = heap_w32 s0 p \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 768 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 768 \<and> heap_w32 st p = heap_w32 s0 p"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (clarsimp simp: word_less_nat_alt)
    apply (cases "unat idx")
     apply (auto simp: unat_word_ariths(1) word_less_nat_alt)
    done
  done

lemma near_init_loop_res_w32_ptr:
  "(whileLoop (\<lambda>idx st. unat idx < 4)
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word)
          \<and> heap_w32 t p = heap_w32 s0 p
          \<and> ptr_valid (heap_typing t) q = ptr_valid (heap_typing s0) q
          \<and> heap_w8 t q = heap_w8 s0 q \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 4 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 4
              \<and> heap_w32 st p = heap_w32 s0 p
              \<and> ptr_valid (heap_typing st) q = ptr_valid (heap_typing s0) q
              \<and> heap_w8 st q = heap_w8 s0 q"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (clarsimp simp: word_less_nat_alt)
    apply (cases "unat idx")
     apply (auto simp: unat_word_ariths(1) word_less_nat_alt)
    done
  done

lemma same_init_loop_res_w32_ptr:
  "(whileLoop (\<lambda>idx st. unat idx < 768)
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (768 :: 32 word)
          \<and> heap_w32 t p = heap_w32 s0 p
          \<and> ptr_valid (heap_typing t) q = ptr_valid (heap_typing s0) q
          \<and> heap_w8 t q = heap_w8 s0 q \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 768 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 768
              \<and> heap_w32 st p = heap_w32 s0 p
              \<and> ptr_valid (heap_typing st) q = ptr_valid (heap_typing s0) q
              \<and> heap_w8 st q = heap_w8 s0 q"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (clarsimp simp: word_less_nat_alt)
    apply (cases "unat idx")
     apply (auto simp: unat_word_ariths(1) word_less_nat_alt)
    done
  done

lemma near_init_loop_res_w32_ptr_buf:
  "(whileLoop (\<lambda>idx st. unat idx < 4)
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word)
          \<and> heap_w32 t p = heap_w32 s0 p
          \<and> ptr_valid (heap_typing t) q = ptr_valid (heap_typing s0) q
          \<and> heap_w8 t q = heap_w8 s0 q
          \<and> buf_valid t buf n = buf_valid s0 buf n \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 4 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 4
              \<and> heap_w32 st p = heap_w32 s0 p
              \<and> ptr_valid (heap_typing st) q = ptr_valid (heap_typing s0) q
              \<and> heap_w8 st q = heap_w8 s0 q
              \<and> buf_valid st buf n = buf_valid s0 buf n"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (clarsimp simp: word_less_nat_alt)
    apply (cases "unat idx")
     apply (auto simp: unat_word_ariths(1) word_less_nat_alt)
    done
  done

lemma same_init_loop_res_w32_ptr_buf:
  "(whileLoop (\<lambda>idx st. unat idx < 768)
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (768 :: 32 word)
          \<and> heap_w32 t p = heap_w32 s0 p
          \<and> ptr_valid (heap_typing t) q = ptr_valid (heap_typing s0) q
          \<and> heap_w8 t q = heap_w8 s0 q
          \<and> buf_valid t buf n = buf_valid s0 buf n \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 768 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 768
              \<and> heap_w32 st p = heap_w32 s0 p
              \<and> ptr_valid (heap_typing st) q = ptr_valid (heap_typing s0) q
              \<and> heap_w8 st q = heap_w8 s0 q
              \<and> buf_valid st buf n = buf_valid s0 buf n"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (clarsimp simp: word_less_nat_alt)
    apply (cases "unat idx")
     apply (auto simp: unat_word_ariths(1) word_less_nat_alt)
    done
  done

lemma vcdiff_decode'_win_ind_len5_nonok_built:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and code_tbl_ready: "code_tbl_built_'' s \<noteq> 0"
      and patch_ok: "buf_valid s patch 5"
      and len_eq: "patch_len = 5"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and magic3_ok: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
      and hdr_ok: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 = 0"
      and app_clear: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 4 = 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] by simp
  have patch4_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 4)"
    using buf_validD[OF patch_ok, of 4] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok code_tbl_ready len_eq magic0_ok magic1_ok magic2_ok magic3_ok
          hdr_ok app_clear patch0_ok patch1_ok patch2_ok patch3_ok patch4_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    subgoal
      apply (rule runs_to_weaken[
        OF near_init_loop_res_w32_ptr
          [where p = out_len and q = "patch +\<^sub>p 5"]])
      apply clarsimp
      apply runs_to_vcg
      subgoal
        apply (rule runs_to_weaken[
          OF same_init_loop_res_w32_ptr
            [where p = out_len and q = "patch +\<^sub>p 5"]])
        apply clarsimp
        apply runs_to_vcg
        apply (simp add: read_byte'_spec)
        apply auto
        done
      done
    done
qed

lemma vcdiff_decode'_win_target_bit_nonok_built:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and code_tbl_ready: "code_tbl_built_'' s \<noteq> 0"
      and patch_ok: "buf_valid s patch 6"
      and len_eq: "patch_len = 6"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and magic3_ok: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
      and hdr_ok: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 = 0"
      and app_clear: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 4 = 0"
      and win_bad: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 2 \<noteq> 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] by simp
  have patch4_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 4)"
    using buf_validD[OF patch_ok, of 4] by simp
  have patch5_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 5)"
    using buf_validD[OF patch_ok, of 5] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok code_tbl_ready len_eq magic0_ok magic1_ok magic2_ok magic3_ok
          hdr_ok app_clear win_bad patch0_ok patch1_ok patch2_ok patch3_ok patch4_ok patch5_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    subgoal
      apply (rule runs_to_weaken[
        OF near_init_loop_res_w32_ptr
          [where p = out_len and q = "patch +\<^sub>p 5"]])
      apply clarsimp
      apply runs_to_vcg
      subgoal
        apply (rule runs_to_weaken[
          OF same_init_loop_res_w32_ptr
            [where p = out_len and q = "patch +\<^sub>p 5"]])
        apply clarsimp
        apply runs_to_vcg
        subgoal for taa
          apply (rule exI[where x =
            "pr_t_C 6 (UCAST(8 \<rightarrow> 32) (heap_w8 taa (patch +\<^sub>p 5))) VCD_OK"])
          apply (rule conjI)
           apply (subst read_byte'_spec[of 5 6 taa patch])
            subgoal using patch5_ok by simp
           subgoal by simp
          apply (intro allI impI)
          subgoal for va
            apply simp
            apply runs_to_vcg
            using win_bad
            apply (auto simp: word_less_nat_alt word_le_nat_alt)
            done
          done
        done
      done
    done
qed

lemma vcdiff_decode'_win_mask_nonok_built:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and code_tbl_ready: "code_tbl_built_'' s \<noteq> 0"
      and patch_ok: "buf_valid s patch 6"
      and len_eq: "patch_len = 6"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and magic3_ok: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
      and hdr_ok: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 = 0"
      and app_clear: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 4 = 0"
      and win_target_clear: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 2 = 0"
      and win_mask_bad: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 0xFFFFFFFA \<noteq> 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] by simp
  have patch4_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 4)"
    using buf_validD[OF patch_ok, of 4] by simp
  have patch5_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 5)"
    using buf_validD[OF patch_ok, of 5] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok code_tbl_ready len_eq magic0_ok magic1_ok magic2_ok magic3_ok
          hdr_ok app_clear win_target_clear win_mask_bad
          patch0_ok patch1_ok patch2_ok patch3_ok patch4_ok patch5_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    subgoal
      apply (rule runs_to_weaken[
        OF near_init_loop_res_w32_ptr
          [where p = out_len and q = "patch +\<^sub>p 5"]])
      apply clarsimp
      apply runs_to_vcg
      subgoal
        apply (rule runs_to_weaken[
          OF same_init_loop_res_w32_ptr
            [where p = out_len and q = "patch +\<^sub>p 5"]])
        apply clarsimp
        apply runs_to_vcg
        subgoal for taa
          apply (rule exI[where x =
            "pr_t_C 6 (UCAST(8 \<rightarrow> 32) (heap_w8 taa (patch +\<^sub>p 5))) VCD_OK"])
          apply (rule conjI)
           apply (subst read_byte'_spec[of 5 6 taa patch])
            subgoal using patch5_ok by simp
           subgoal by simp
          apply (intro allI impI)
          subgoal for va
            apply simp
            apply runs_to_vcg
            using win_target_clear win_mask_bad
            apply (auto simp: word_less_nat_alt word_le_nat_alt)
            done
          done
        done
      done
    done
qed

lemma vcdiff_decode'_win_srcneed_nonok_built:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and code_tbl_ready: "code_tbl_built_'' s \<noteq> 0"
      and patch_ok: "buf_valid s patch 6"
      and len_eq: "patch_len = 6"
      and src_null: "src = NULL"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and magic3_ok: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
      and hdr_ok: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 = 0"
      and app_clear: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 4 = 0"
      and win_src_set: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 1 = 1"
      and win_target_clear: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 2 = 0"
      and win_mask_clear: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 0xFFFFFFFA = 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<and> heap_w32 t out_len = (0 :: 32 word) \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] by simp
  have patch4_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 4)"
    using buf_validD[OF patch_ok, of 4] by simp
  have patch5_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 5)"
    using buf_validD[OF patch_ok, of 5] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok code_tbl_ready len_eq src_null magic0_ok magic1_ok magic2_ok magic3_ok
          hdr_ok app_clear win_src_set win_target_clear win_mask_clear
          patch0_ok patch1_ok patch2_ok patch3_ok patch4_ok patch5_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    subgoal
      apply (rule runs_to_weaken[
        OF near_init_loop_res_w32_ptr
          [where p = out_len and q = "patch +\<^sub>p 5"]])
      apply clarsimp
      apply runs_to_vcg
      subgoal
        apply (rule runs_to_weaken[
          OF same_init_loop_res_w32_ptr
            [where p = out_len and q = "patch +\<^sub>p 5"]])
        apply clarsimp
        apply runs_to_vcg
        subgoal for taa
          apply (rule exI[where x =
            "pr_t_C 6 (UCAST(8 \<rightarrow> 32) (heap_w8 taa (patch +\<^sub>p 5))) VCD_OK"])
          apply (rule conjI)
           apply (subst read_byte'_spec[of 5 6 taa patch])
            subgoal using patch5_ok by simp
           subgoal by simp
          apply (intro allI impI)
          subgoal for va
            apply simp
            apply runs_to_vcg
            using src_null win_src_set win_target_clear win_mask_clear
            apply (auto simp: word_less_nat_alt word_le_nat_alt)
            done
          done
        done
      done
    done
qed

lemma vcdiff_decode'_win_ind_len5_nonok_weak:
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch 5"
      and len_eq: "patch_len = 5"
      and magic0_ok: "uint (heap_w8 s patch) = 214"
      and magic1_ok: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
      and magic2_ok: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
      and magic3_ok: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
      and hdr_ok: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 = 0"
      and app_clear: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 4 = 0"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. r \<noteq> Result 0 \<rbrace>"
proof (cases "code_tbl_built_'' s = 0")
  case False
  show ?thesis
    by (rule runs_to_weaken[OF vcdiff_decode'_win_ind_len5_nonok_built
        [OF out_len_ok False patch_ok len_eq magic0_ok magic1_ok magic2_ok magic3_ok hdr_ok app_clear]])
       simp
next
  case True
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] by simp
  have patch4_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 4)"
    using buf_validD[OF patch_ok, of 4] by simp
  show ?thesis
    unfolding vcdiff_decode'_def
    apply runs_to_vcg
    using out_len_ok True len_eq magic0_ok magic1_ok magic2_ok magic3_ok hdr_ok app_clear
          patch0_ok patch1_ok patch2_ok patch3_ok patch4_ok
    apply (auto simp: word_less_nat_alt word_le_nat_alt)
    subgoal
      apply (rule runs_to_weaken[OF build_code_table'_spec])
      apply clarsimp
      apply runs_to_vcg
      subgoal
        apply (rule runs_to_weaken[
          OF near_init_loop_res_w32_ptr[where p = out_len and q = "patch +\<^sub>p 5"]])
        apply clarsimp
        apply runs_to_vcg
        subgoal
          apply (rule runs_to_weaken[
            OF same_init_loop_res_w32_ptr[where p = out_len and q = "patch +\<^sub>p 5"]])
          apply clarsimp
          apply runs_to_vcg
          apply (simp add: read_byte'_spec)
          apply auto
          done
        done
      done
    done
qed

(* ---------- Phase 2: Header + window parse refinement ---------- *)

(*
  cache_abs_init: after the near/same init loops zero out the arrays,
  the C state corresponds to cache_init with near_ptr = 0.
*)
lemma cache_abs_init_zero:
  assumes near_zero: "\<forall>i < (4::nat). near_arr_'' s .[i] = (0 :: 32 word)"
      and same_zero: "\<forall>i < (768::nat). same_arr_'' s .[i] = (0 :: 32 word)"
  shows "cache_abs s cache_init 0"
proof (unfold cache_abs_def, intro conjI)
  show "length (near cache_init) = s_near"
    by (simp add: cache_init_def s_near_def)
  show "length (same cache_init) = same_buckets"
    by (simp add: cache_init_def same_buckets_def s_same_def)
  show "unat (0 :: 32 word) < s_near"
    by (simp add: s_near_def)
  show "near_ptr cache_init = unat (0 :: 32 word)"
    by (simp add: cache_init_def)
  show "\<forall>i < s_near. near_arr_'' s .[i] = of_nat (near cache_init ! i)"
  proof (intro allI impI)
    fix i :: nat assume "i < s_near"
    hence "i < 4" by (simp add: s_near_def)
    have near_is_rep: "near cache_init = replicate 4 (0::nat)"
      by (simp add: cache_init_def s_near_def)
    have "near cache_init ! i = 0"
      using \<open>i < 4\<close>
      by (simp only: near_is_rep nth_replicate)
    thus "near_arr_'' s .[i] = of_nat (near cache_init ! i)"
      using near_zero \<open>i < 4\<close> by simp
  qed
  show "\<forall>i < same_buckets. same_arr_'' s .[i] = of_nat (same cache_init ! i)"
  proof (intro allI impI)
    fix i :: nat assume "i < same_buckets"
    hence "i < 768" by (simp add: same_buckets_def s_same_def)
    have len_same: "length (same cache_init) = 768"
      by (simp add: cache_init_def same_buckets_def s_same_def)
    have same_is_rep: "same cache_init = replicate 768 (0::nat)"
      by (simp add: cache_init_def same_buckets_def s_same_def)
    have "same cache_init ! i = 0"
      using \<open>i < 768\<close>
      by (simp only: same_is_rep nth_replicate)
    thus "same_arr_'' s .[i] = of_nat (same cache_init ! i)"
      using same_zero \<open>i < 768\<close> by simp
  qed
qed

(*
  Near-init loop: stronger postcondition that guarantees all slots are zero.
*)
lemma near_init_loop_zeros:
  "(whileLoop (\<lambda>idx st. unat idx < 4)
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word)
          \<and> (\<forall>i < (4::nat). near_arr_'' t .[i] = (0 :: 32 word))
          \<and> heap_w8 t = heap_w8 s0
          \<and> heap_w32 t = heap_w32 s0
          \<and> same_arr_'' t = same_arr_'' s0
          \<and> code_tbl_'' t = code_tbl_'' s0
          \<and> code_tbl_built_'' t = code_tbl_built_'' s0
          \<and> heap_typing t = heap_typing s0 \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 4 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 4
              \<and> (\<forall>i < unat idx. near_arr_'' st .[i] = (0 :: 32 word))
              \<and> heap_w8 st = heap_w8 s0
              \<and> heap_w32 st = heap_w32 s0
              \<and> same_arr_'' st = same_arr_'' s0
              \<and> code_tbl_'' st = code_tbl_'' s0
              \<and> code_tbl_built_'' st = code_tbl_built_'' s0
              \<and> heap_typing st = heap_typing s0"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt unat_word_ariths(1))
    subgoal for i
      apply (cases "i = unat idx")
       apply simp
      apply (subgoal_tac "i < unat idx")
       apply simp
      apply (simp add: less_Suc_eq)
      done
    done
  done

(*
  Same-init loop: stronger postcondition that guarantees all slots are zero.
*)
lemma same_init_loop_zeros:
  "(whileLoop (\<lambda>idx st. unat idx < 768)
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (768 :: 32 word)
          \<and> (\<forall>i < (768::nat). same_arr_'' t .[i] = (0 :: 32 word))
          \<and> heap_w8 t = heap_w8 s0
          \<and> heap_w32 t = heap_w32 s0
          \<and> near_arr_'' t = near_arr_'' s0
          \<and> code_tbl_'' t = code_tbl_'' s0
          \<and> code_tbl_built_'' t = code_tbl_built_'' s0
          \<and> heap_typing t = heap_typing s0 \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 768 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 768
              \<and> (\<forall>i < unat idx. same_arr_'' st .[i] = (0 :: 32 word))
              \<and> heap_w8 st = heap_w8 s0
              \<and> heap_w32 st = heap_w32 s0
              \<and> near_arr_'' st = near_arr_'' s0
              \<and> code_tbl_'' st = code_tbl_'' s0
              \<and> code_tbl_built_'' st = code_tbl_built_'' s0
              \<and> heap_typing st = heap_typing s0"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (simp_all add: word_less_nat_alt unat_word_ariths(1))
    subgoal for i
      apply (cases "i = unat idx")
       apply simp
      apply (subgoal_tac "i < unat idx")
       apply simp
      apply (simp add: less_Suc_eq)
      done
    done
  done

(*
  Header parse prefix refinement (no-source, no-app-header, code_tbl built).

  This is the simplest success-path scenario. Shows that the C decoder
  reaches the main while-loop entry with cursors matching parse_window.

  Assumptions on the patch buffer:
    - Magic: D6 C3 C4 00
    - Hdr_Indicator: low 2 bits clear, bit 2 clear (no app header)
    - win_ind: VCD_SOURCE clear (0x01 bit = 0), VCD_TARGET clear, mask clear
    - Varints for dlen, tgt_len, di=0, data_len, inst_len, addr_len all parse
    - No Adler32 (win_ind bit 2 = 0)
    - Section sizes consistent: data_len + inst_len + addr_len fits in remaining

  Under these, after header parsing, the C state has:
    - data_cursor, inst_cursor, addr_cursor pointing into the patch buffer
    - tgt_pos = 0
    - near_ptr = 0
    - near_arr all zero, same_arr all zero (cache_abs cache_init 0)
    - code_tbl_matches holds
    - heap_bytes of patch and src unchanged
*)

(*
  Helper: read_varint' applied to a specific position in the patch buffer,
  used to chain multiple varint reads.
*)
lemma rest_len_le:
  assumes "varint_decode (drop k bs) = Some (nv, rest)"
  shows "length rest \<le> length bs - k"
proof -
  have "length rest \<le> length (drop k bs)"
    by (rule varint_decode_length[OF assms])
  thus ?thesis by simp
qed

lemma read_varint'_chain:
  assumes buf_ok: "buf_valid s buf (unat len)"
      and pos_ok: "pos \<le> len"
      and decode_ok: "varint_decode (drop (unat pos) (heap_bytes s buf (unat len)))
                     = Some (nv, rest)"
      and nv_fits: "nv < 2 ^ 32"
  shows "read_varint' buf len pos \<bullet> s
           \<lbrace> \<lambda>r t. t = s \<and>
                  r = Result (pr_t_C (len - of_nat (length rest))
                                     (of_nat nv) VCD_OK) \<and>
                  pos \<le> len - of_nat (length rest) \<and>
                  len - of_nat (length rest) \<le> len \<rbrace>"
proof -
  let ?new_pos = "len - of_nat (length rest) :: 32 word"
  have rest_le_input: "length rest \<le> length (drop (unat pos) (heap_bytes s buf (unat len)))"
    by (rule varint_decode_length[OF decode_ok])
  hence rest_le_len: "length rest \<le> unat len"
    by simp
  have rest_lt_2p32: "length rest < 2 ^ 32"
    using rest_le_len unat_lt2p[of len] by simp
  have unat_rest_word: "unat (of_nat (length rest) :: 32 word) = length rest"
    using rest_lt_2p32 by (simp add: unat_of_nat_eq)
  have rest_word_le_len: "(of_nat (length rest) :: 32 word) \<le> len"
    using rest_le_len unat_rest_word by (simp add: word_le_nat_alt)
  have unat_new_pos: "unat ?new_pos = unat len - length rest"
    using rest_word_le_len unat_rest_word by (simp add: unat_sub)
  have goal_post: "\<And>r t.
    t = s \<and> (\<exists>v. r = Result v \<and>
         pos \<le> pr_t_C.pos_C v \<and> pr_t_C.pos_C v \<le> len \<and>
         (case varint_decode (drop (unat pos) (heap_bytes s buf (unat len))) of
            Some (nv, rest) \<Rightarrow> pr_t_C.err_C v = VCD_OK \<and>
               unat (pr_t_C.pos_C v) = unat len - length rest \<and>
               nv = unat (pr_t_C.val_C v)
          | None \<Rightarrow> pr_t_C.err_C v \<noteq> VCD_OK))
    \<Longrightarrow> t = s \<and> r = Result (pr_t_C ?new_pos (of_nat nv) VCD_OK) \<and>
        pos \<le> ?new_pos \<and> ?new_pos \<le> len"
  proof -
    fix r t
    assume H: "t = s \<and> (\<exists>v. r = Result v \<and>
         pos \<le> pr_t_C.pos_C v \<and> pr_t_C.pos_C v \<le> len \<and>
         (case varint_decode (drop (unat pos) (heap_bytes s buf (unat len))) of
            Some (nv, rest) \<Rightarrow> pr_t_C.err_C v = VCD_OK \<and>
               unat (pr_t_C.pos_C v) = unat len - length rest \<and>
               nv = unat (pr_t_C.val_C v)
          | None \<Rightarrow> pr_t_C.err_C v \<noteq> VCD_OK))"
    from H obtain v where ts: "t = s" and rv: "r = Result v"
      and pv_le: "pos \<le> pr_t_C.pos_C v" and pv_le_len: "pr_t_C.pos_C v \<le> len"
      and err_ok: "pr_t_C.err_C v = VCD_OK"
      and pos_unat: "unat (pr_t_C.pos_C v) = unat len - length rest"
      and nv_unat: "nv = unat (pr_t_C.val_C v)"
      using decode_ok by (auto split: option.splits)
    have pos_eq: "pr_t_C.pos_C v = ?new_pos"
      using pos_unat unat_new_pos by (simp add: word_unat_eq_iff)
    have val_eq: "pr_t_C.val_C v = of_nat nv"
      using nv_unat nv_fits by (simp add: word_unat_eq_iff unat_of_nat_eq)
    have v_eq: "v = pr_t_C ?new_pos (of_nat nv) VCD_OK"
      using pos_eq val_eq err_ok by (cases v) simp
    show "t = s \<and> r = Result (pr_t_C ?new_pos (of_nat nv) VCD_OK) \<and>
          pos \<le> ?new_pos \<and> ?new_pos \<le> len"
      using ts rv v_eq pv_le pv_le_len pos_eq by simp
  qed
  show ?thesis
    by (rule runs_to_weaken[OF read_varint'_spec[OF buf_ok pos_ok] goal_post])
qed

(*
  Helper: read_byte at a known valid position gives the heap byte.
  This wraps read_byte'_spec into a runs_to form for composition.
*)
lemma read_byte'_chain:
  assumes "unat pos < unat len"
      and "ptr_valid (heap_typing s) (buf +\<^sub>p uint pos)"
  shows "read_byte' buf len pos s =
           Some (pr_t_C (pos + 1) (UCAST(8 \<rightarrow> 32) (heap_w8 s (buf +\<^sub>p uint pos))) VCD_OK)"
proof -
  have "pos < len" using assms(1) by (simp add: word_less_nat_alt)
  thus ?thesis using assms(2) by (simp add: read_byte'_spec)
qed

(*
  parse_header correspondence: relates the C's initial byte checks to
  parse_header on the heap_bytes view.

  Under the no-app-header case (hi & 0x04 == 0), parse_header succeeds
  and returns `drop 5 patch_bytes`.
*)
lemma parse_header_no_app:
  assumes bytes_def: "bs = heap_bytes s patch (unat patch_len)"
      and len_ok: "5 \<le> unat patch_len"
      and magic0: "bs ! 0 = 0xD6"
      and magic1: "bs ! 1 = 0xC3"
      and magic2: "bs ! 2 = 0xC4"
      and magic3: "bs ! 3 = 0x00"
      and hdr_ok: "bs ! 4 AND 0x03 = 0"
      and no_app: "bs ! 4 AND 0x04 = 0"
  shows "parse_header bs = Inl (drop 5 bs)"
proof -
  have len_ge: "length bs \<ge> 5" using len_ok by (simp add: bytes_def)
  obtain b0 bs1 where decomp1: "bs = b0 # bs1" "length bs1 \<ge> 4"
    using len_ge by (cases bs) auto
  obtain b1 bs2 where decomp2: "bs1 = b1 # bs2" "length bs2 \<ge> 3"
    using decomp1(2) by (cases bs1) auto
  obtain b2 bs3 where decomp3: "bs2 = b2 # bs3" "length bs3 \<ge> 2"
    using decomp2(2) by (cases bs2) auto
  obtain b3 bs4 where decomp4: "bs3 = b3 # bs4" "length bs4 \<ge> 1"
    using decomp3(2) by (cases bs3) auto
  obtain hi rest5 where decomp5: "bs4 = hi # rest5"
    using decomp4(2) by (cases bs4) auto
  have bs_eq: "bs = b0 # b1 # b2 # b3 # hi # rest5"
    using decomp1(1) decomp2(1) decomp3(1) decomp4(1) decomp5 by simp
  have b0: "b0 = 0xD6" using magic0 bs_eq by simp
  have b1: "b1 = 0xC3" using magic1 bs_eq by simp
  have b2: "b2 = 0xC4" using magic2 bs_eq by simp
  have b3: "b3 = 0x00" using magic3 bs_eq by simp
  have hi_hdr: "hi AND 0x03 = 0" using hdr_ok bs_eq by simp
  have hi_app: "hi AND 0x04 = 0" using no_app bs_eq by simp
  show ?thesis
    unfolding parse_header_def bs_eq
    using b0 b1 b2 b3 hi_hdr hi_app
    by simp
qed

(*
  parse_window correspondence for the no-source case.

  When win_ind has VCD_SOURCE clear (bit 0 = 0) and VCD_TARGET clear (bit 1 = 0),
  and mask bits clear, parse_window parses:
    - win_ind byte (already consumed by read_byte)
    - 0 src_seg_len, 0 src_seg_off (no source)
    - dlen varint
    - tgt_len varint
    - di byte (must be 0)
    - data_len varint
    - inst_len varint
    - addr_len varint

  We express this as: given the byte list starting after the header (i.e. drop 5 bs),
  if the first byte has certain properties and the varints parse correctly,
  parse_window returns the expected parsed_window record.
*)
lemma parse_window_no_source:
  assumes win_byte: "pop_byte wbs = Some (win_ind, wbs1)"
      and no_target: "win_ind AND 0x02 = 0"
      and mask_ok: "win_ind AND 0xFA = 0"
      and no_source: "win_ind AND 0x01 = 0"
      and no_adler: "win_ind AND 0x04 = 0"
      and dlen_ok: "varint_decode wbs1 = Some (dlen, wbs2)"
      and tgt_ok: "varint_decode wbs2 = Some (tgt_len, wbs3)"
      and di_pop: "pop_byte wbs3 = Some (di, wbs4)"
      and di_zero: "di = 0"
      and data_ok: "varint_decode wbs4 = Some (data_len, wbs5)"
      and inst_ok: "varint_decode wbs5 = Some (inst_len, wbs6)"
      and addr_ok: "varint_decode wbs6 = Some (addr_len, wbs7)"
      and sizes_ok: "data_len + inst_len + addr_len \<le> length wbs7"
      and dlen_exact: "dlen = (length wbs2 - length wbs7) + data_len + inst_len + addr_len"
  shows "parse_window wbs = Inl (\<lparr>
           pw_src_seg_len = 0,
           pw_src_seg_off = 0,
           pw_tgt_len = tgt_len,
           pw_data = take data_len wbs7,
           pw_inst = take inst_len (drop data_len wbs7),
           pw_addr = take addr_len (drop (data_len + inst_len) wbs7)
         \<rparr>, drop (data_len + inst_len + addr_len) wbs7)"
  unfolding parse_window_def
  using win_byte no_target mask_ok no_source dlen_ok tgt_ok di_pop di_zero
        data_ok inst_ok addr_ok sizes_ok no_adler dlen_exact
  by (simp add: pop_byte_def Let_def add.commute add.left_commute
           split: list.splits option.splits)

lemma parse_window_with_source:
  assumes win_byte: "pop_byte wbs = Some (win_ind, wbs1)"
      and no_target: "win_ind AND 0x02 = 0"
      and mask_ok: "win_ind AND 0xFA = 0"
      and has_source: "win_ind AND 0x01 \<noteq> 0"
      and no_adler: "win_ind AND 0x04 = 0"
      and sl_ok: "varint_decode wbs1 = Some (src_seg_len, wbs1a)"
      and so_ok: "varint_decode wbs1a = Some (src_seg_off, wbs3)"
      and dlen_ok: "varint_decode wbs3 = Some (dlen, wbs4)"
      and tgt_ok: "varint_decode wbs4 = Some (tgt_len, wbs5)"
      and di_pop: "pop_byte wbs5 = Some (di, wbs6)"
      and di_zero: "di = 0"
      and data_ok: "varint_decode wbs6 = Some (data_len, wbs7)"
      and inst_ok: "varint_decode wbs7 = Some (inst_len, wbs8)"
      and addr_ok: "varint_decode wbs8 = Some (addr_len, wbs9)"
      and sizes_ok: "data_len + inst_len + addr_len \<le> length wbs9"
      and dlen_exact: "dlen = (length wbs4 - length wbs9) + data_len + inst_len + addr_len"
  shows "parse_window wbs = Inl (\<lparr>
           pw_src_seg_len = src_seg_len,
           pw_src_seg_off = src_seg_off,
           pw_tgt_len = tgt_len,
           pw_data = take data_len wbs9,
           pw_inst = take inst_len (drop data_len wbs9),
           pw_addr = take addr_len (drop (data_len + inst_len) wbs9)
         \<rparr>, drop (data_len + inst_len + addr_len) wbs9)"
  unfolding parse_window_def
  using win_byte no_target mask_ok has_source sl_ok so_ok dlen_ok tgt_ok
        di_pop di_zero data_ok inst_ok addr_ok sizes_ok no_adler dlen_exact
  by (simp add: pop_byte_def Let_def add.commute add.left_commute
           split: list.splits option.splits)

lemma parse_window_no_source_adler_general:
  assumes win_byte: "pop_byte wbs = Some (win_ind, wbs1)"
      and no_target: "win_ind AND 0x02 = 0"
      and mask_ok: "win_ind AND 0xFA = 0"
      and no_source: "win_ind AND 0x01 = 0"
      and adler_len: "alen = (if win_ind AND 0x04 \<noteq> 0 then 4 else 0)"
      and dlen_ok: "varint_decode wbs1 = Some (dlen, wbs2)"
      and tgt_ok: "varint_decode wbs2 = Some (tgt_len, wbs3)"
      and di_pop: "pop_byte wbs3 = Some (di, wbs4)"
      and di_zero: "di = 0"
      and data_ok: "varint_decode wbs4 = Some (data_len, wbs5)"
      and inst_ok: "varint_decode wbs5 = Some (inst_len, wbs6)"
      and addr_ok: "varint_decode wbs6 = Some (addr_len, wbs7)"
      and sizes_ok: "alen + data_len + inst_len + addr_len \<le> length wbs7"
      and dlen_exact: "dlen = (length wbs2 - length wbs7) + alen + data_len + inst_len + addr_len"
  shows "parse_window wbs = Inl (\<lparr>
           pw_src_seg_len = 0,
           pw_src_seg_off = 0,
           pw_tgt_len = tgt_len,
           pw_data = take data_len (drop alen wbs7),
           pw_inst = take inst_len (drop (alen + data_len) wbs7),
           pw_addr = take addr_len (drop (alen + data_len + inst_len) wbs7)
         \<rparr>, drop (alen + data_len + inst_len + addr_len) wbs7)"
  unfolding parse_window_def
  using win_byte no_target mask_ok no_source adler_len dlen_ok tgt_ok di_pop di_zero
        data_ok inst_ok addr_ok sizes_ok dlen_exact
  by (simp add: pop_byte_def Let_def add.commute add.left_commute add.assoc
                drop_drop
         split: list.splits option.splits)

lemma parse_window_with_source_adler_general:
  assumes win_byte: "pop_byte wbs = Some (win_ind, wbs1)"
      and no_target: "win_ind AND 0x02 = 0"
      and mask_ok: "win_ind AND 0xFA = 0"
      and has_source: "win_ind AND 0x01 \<noteq> 0"
      and adler_len: "alen = (if win_ind AND 0x04 \<noteq> 0 then 4 else 0)"
      and sl_ok: "varint_decode wbs1 = Some (src_seg_len, wbs1a)"
      and so_ok: "varint_decode wbs1a = Some (src_seg_off, wbs3)"
      and dlen_ok: "varint_decode wbs3 = Some (dlen, wbs4)"
      and tgt_ok: "varint_decode wbs4 = Some (tgt_len, wbs5)"
      and di_pop: "pop_byte wbs5 = Some (di, wbs6)"
      and di_zero: "di = 0"
      and data_ok: "varint_decode wbs6 = Some (data_len, wbs7)"
      and inst_ok: "varint_decode wbs7 = Some (inst_len, wbs8)"
      and addr_ok: "varint_decode wbs8 = Some (addr_len, wbs9)"
      and sizes_ok: "alen + data_len + inst_len + addr_len \<le> length wbs9"
      and dlen_exact: "dlen = (length wbs4 - length wbs9) + alen + data_len + inst_len + addr_len"
  shows "parse_window wbs = Inl (\<lparr>
           pw_src_seg_len = src_seg_len,
           pw_src_seg_off = src_seg_off,
           pw_tgt_len = tgt_len,
           pw_data = take data_len (drop alen wbs9),
           pw_inst = take inst_len (drop (alen + data_len) wbs9),
           pw_addr = take addr_len (drop (alen + data_len + inst_len) wbs9)
         \<rparr>, drop (alen + data_len + inst_len + addr_len) wbs9)"
  unfolding parse_window_def
  using win_byte no_target mask_ok has_source adler_len sl_ok so_ok dlen_ok tgt_ok
        di_pop di_zero data_ok inst_ok addr_ok sizes_ok dlen_exact
  by (simp add: pop_byte_def Let_def add.commute add.left_commute add.assoc
                drop_drop
         split: list.splits option.splits)

lemma parse_window_drop_byte_bits:
  assumes parsed: "parse_window (drop k bs) = Inl x"
      and k_lt: "k < length bs"
  shows "(bs ! k) AND 0x02 = 0"
    and "(bs ! k) AND 0xFA = 0"
proof -
  have drop_eq: "drop k bs = bs ! k # drop (Suc k) bs"
    using k_lt by (simp add: Cons_nth_drop_Suc)
  show "(bs ! k) AND 0x02 = 0"
    using parsed unfolding parse_window_def drop_eq pop_byte_def
    by (auto split: if_splits option.splits)
  show "(bs ! k) AND 0xFA = 0"
    using parsed unfolding parse_window_def drop_eq pop_byte_def
    by (auto split: if_splits option.splits)
qed

lemma parse_window_source_prefix_decodes:
  assumes parsed: "parse_window (drop k bs) = Inl (win, tail)"
      and k_lt: "k < length bs"
      and source_set: "(bs ! k) AND 0x01 \<noteq> 0"
  shows "\<exists>rest1 rest2 rest3 dlen.
           varint_decode (drop (Suc k) bs) =
             Some (pw_src_seg_len win, rest1) \<and>
           varint_decode rest1 = Some (pw_src_seg_off win, rest2) \<and>
           varint_decode rest2 = Some (dlen, rest3)"
proof -
  have drop_eq: "drop k bs = bs ! k # drop (Suc k) bs"
    using k_lt by (simp add: Cons_nth_drop_Suc)
  show ?thesis
    using parsed source_set
    unfolding parse_window_def drop_eq pop_byte_def
    by (auto simp: Let_def split: if_splits option.splits)
qed

lemma parse_window_source_full_decodes:
  assumes parsed: "parse_window (drop k bs) = Inl (win, tail)"
      and k_lt: "k < length bs"
      and source_set: "(bs ! k) AND 0x01 \<noteq> 0"
  shows "\<exists>rest1 rest2 rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len.
           varint_decode (drop (Suc k) bs) =
             Some (pw_src_seg_len win, rest1) \<and>
           varint_decode rest1 = Some (pw_src_seg_off win, rest2) \<and>
           varint_decode rest2 = Some (dlen, rest3) \<and>
           varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
           pop_byte rest4 = Some (0, rest5) \<and>
           varint_decode rest5 = Some (data_len, rest6) \<and>
           varint_decode rest6 = Some (inst_len, rest7) \<and>
           varint_decode rest7 = Some (addr_len, rest8) \<and>
           (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) +
             data_len + inst_len + addr_len \<le> length rest8 \<and>
           dlen = (length rest3 - length rest8) +
                  (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) +
                  data_len + inst_len + addr_len"
proof -
  have drop_eq: "drop k bs = bs ! k # drop (Suc k) bs"
    using k_lt by (simp add: Cons_nth_drop_Suc)
  obtain rest1 rest2 rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len where
    dec1: "varint_decode (drop (Suc k) bs) = Some (pw_src_seg_len win, rest1)"
    and dec2: "varint_decode rest1 = Some (pw_src_seg_off win, rest2)"
    and dec3: "varint_decode rest2 = Some (dlen, rest3)"
    and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
    and di0: "pop_byte rest4 = Some (0, rest5)"
    and dec5: "varint_decode rest5 = Some (data_len, rest6)"
    and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
    and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
    and dlen_ge: "\<not> dlen < length rest3 - length rest8"
    and dlen_rem:
      "dlen - (length rest3 - length rest8) =
         (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) + data_len + inst_len + addr_len"
    and payload_fit:
      "\<not> length rest8 <
         (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) + data_len + inst_len + addr_len"
    using parsed source_set
    unfolding parse_window_def drop_eq pop_byte_def
    by (auto simp: Let_def split: if_splits option.splits)
  have sizes_ok:
    "(if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) +
       data_len + inst_len + addr_len \<le> length rest8"
    using payload_fit by simp
  have dlen_exact:
    "dlen = (length rest3 - length rest8) +
            (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) +
            data_len + inst_len + addr_len"
    using dlen_ge dlen_rem by arith
  show ?thesis
    using dec1 dec2 dec3 dec4 di0 dec5 dec6 dec7 sizes_ok dlen_exact by blast
qed

lemma parse_window_no_source_full_decodes:
  assumes parsed: "parse_window (drop k bs) = Inl (win, tail)"
      and k_lt: "k < length bs"
      and no_source: "(bs ! k) AND 0x01 = 0"
  shows "\<exists>rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len.
           varint_decode (drop (Suc k) bs) = Some (dlen, rest3) \<and>
           varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
           pop_byte rest4 = Some (0, rest5) \<and>
           varint_decode rest5 = Some (data_len, rest6) \<and>
           varint_decode rest6 = Some (inst_len, rest7) \<and>
           varint_decode rest7 = Some (addr_len, rest8) \<and>
           (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) +
             data_len + inst_len + addr_len \<le> length rest8 \<and>
           dlen = (length rest3 - length rest8) +
                  (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) +
                  data_len + inst_len + addr_len"
proof -
  have drop_eq: "drop k bs = bs ! k # drop (Suc k) bs"
    using k_lt by (simp add: Cons_nth_drop_Suc)
  obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len where
    dec3: "varint_decode (drop (Suc k) bs) = Some (dlen, rest3)"
    and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
    and di0: "pop_byte rest4 = Some (0, rest5)"
    and dec5: "varint_decode rest5 = Some (data_len, rest6)"
    and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
    and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
    and dlen_ge: "\<not> dlen < length rest3 - length rest8"
    and dlen_rem:
      "dlen - (length rest3 - length rest8) =
         (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) + data_len + inst_len + addr_len"
    and payload_fit:
      "\<not> length rest8 <
         (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) + data_len + inst_len + addr_len"
    using parsed no_source
    unfolding parse_window_def drop_eq pop_byte_def
    by (auto simp: Let_def split: if_splits option.splits)
  have sizes_ok:
    "(if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) +
       data_len + inst_len + addr_len \<le> length rest8"
    using payload_fit by simp
  have dlen_exact:
    "dlen = (length rest3 - length rest8) +
            (if (bs ! k) AND 0x04 \<noteq> 0 then 4 else 0) +
            data_len + inst_len + addr_len"
    using dlen_ge dlen_rem by arith
  show ?thesis
    using dec3 dec4 di0 dec5 dec6 dec7 sizes_ok dlen_exact by blast
qed

(* ---------- Phase 1: Output-write infrastructure ---------- *)

(*
  Buffer disjointness: no overlap between two pointer regions.
  Used to show writes to `out` don't affect reads from `patch`/`src`.
*)
definition bufs_disjoint :: "8 word ptr \<Rightarrow> nat \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "bufs_disjoint p pn q qn =
     (\<forall>i < pn. \<forall>j < qn. p +\<^sub>p int i \<noteq> q +\<^sub>p int j)"

lemma bufs_disjoint_sym:
  "bufs_disjoint p pn q qn = bufs_disjoint q qn p pn"
  unfolding bufs_disjoint_def by (auto simp: eq_commute)

(*
  Key preservation lemma: writing a byte to a pointer outside a buffer region
  does not change the heap_bytes view of that region.
*)
lemma heap_bytes_update_disjoint:
  assumes disj: "bufs_disjoint buf n (Ptr (ptr_val ptr)) 1"
  shows "heap_bytes (heap_w8_update (\<lambda>h. h(ptr := v)) s) buf n =
         heap_bytes s buf n"
proof -
  have "\<forall>i < n. buf +\<^sub>p int i \<noteq> ptr"
  proof (intro allI impI)
    fix i assume "i < n"
    from disj have "buf +\<^sub>p int i \<noteq> Ptr (ptr_val ptr) +\<^sub>p int 0"
      unfolding bufs_disjoint_def using \<open>i < n\<close> by auto
    thus "buf +\<^sub>p int i \<noteq> ptr" by simp
  qed
  thus ?thesis
    by (simp add: heap_bytes_def fun_upd_apply)
qed

(*
  Simpler version: if the written pointer is NOT in the buffer range,
  heap_bytes is preserved.
*)
lemma heap_bytes_update_outside:
  assumes "\<forall>i < n. buf +\<^sub>p int i \<noteq> ptr"
  shows "heap_bytes (heap_w8_update (\<lambda>h. h(ptr := v)) s) buf n =
         heap_bytes s buf n"
  using assms by (simp add: heap_bytes_def fun_upd_apply)

(*
  buf_valid is not affected by heap_w8 updates (it only depends on heap_typing).
*)
lemma buf_valid_heap_w8_update_any[simp]:
  "buf_valid (heap_w8_update f s) buf n = buf_valid s buf n"
  by (simp add: buf_valid_def)

(*
  Writing a byte to the heap does not affect heap_w32 reads
  (type separation between 8-bit and 32-bit heaps).
*)
lemma heap_w32_heap_w8_update[simp]:
  "heap_w32 (heap_w8_update f s) p = heap_w32 s p"
  by simp

(*
  ptr_valid is not affected by heap_w8 updates.
*)
lemma ptr_valid_heap_w8_update[simp]:
  "ptr_valid (heap_typing (heap_w8_update f s)) p =
   ptr_valid (heap_typing s) p"
  by simp

(*
  Extending heap_bytes by one position: if we write v at buf +p n,
  the resulting heap_bytes of length (n+1) is the old heap_bytes of length n
  appended with [v].
*)
lemma heap_bytes_extend:
  assumes disj: "\<forall>i < n. buf +\<^sub>p int i \<noteq> buf +\<^sub>p int n"
  shows "heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int n := v)) s) buf (Suc n) =
         heap_bytes s buf n @ [v]"
proof (rule nth_equalityI)
  show "length (heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int n := v)) s) buf (Suc n)) =
        length (heap_bytes s buf n @ [v])"
    by simp
next
  fix i assume "i < length (heap_bytes (heap_w8_update (\<lambda>h. h(buf +\<^sub>p int n := v)) s) buf (Suc n))"
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

(*
  The init loops preserve buf_valid AND heap_bytes of the patch buffer.
  Composition lemma: after near_init + same_init, the patch buffer is
  still valid and its contents are unchanged.
*)
lemma init_loops_preserve_patch:
  assumes "heap_w8 t = heap_w8 s" and "heap_typing t = heap_typing s"
  shows "buf_valid t buf n = buf_valid s buf n"
    and "heap_bytes t buf n = heap_bytes s buf n"
  using assms by (simp_all add: buf_valid_def heap_bytes_def)

(*
  varint_decode_loop returns a suffix: the result 'rest' satisfies
  drop (length bs - length rest) bs = rest.
*)
lemma varint_decode_loop_suffix:
  "varint_decode_loop fuel acc bs = Some (v, rest) \<Longrightarrow> suffix rest bs"
proof (induction fuel acc bs rule: varint_decode_loop.induct)
  case (1 acc bs) thus ?case by simp
next
  case (2 fuel acc) thus ?case by simp
next
  case (3 fuel acc b rest')
  show ?case
  proof (cases "b AND 0x80 = 0")
    case True
    with 3 show ?thesis
      by (auto simp: Let_def split: if_splits intro: suffix_ConsI)
  next
    case False
    with 3 show ?thesis
      by (auto simp: Let_def intro: suffix_ConsI)
  qed
qed

lemma varint_decode_suffix:
  "varint_decode bs = Some (v, rest) \<Longrightarrow> suffix rest bs"
  unfolding varint_decode_def by (rule varint_decode_loop_suffix)

lemma varint_decode_drop_rest:
  assumes dec: "varint_decode (drop k bs) = Some (v, rest)"
  shows "drop (length bs - length rest) bs = rest"
proof -
  have suf: "suffix rest (drop k bs)"
    by (rule varint_decode_suffix[OF dec])
  then obtain pfx where eq: "drop k bs = pfx @ rest"
    by (auto simp: suffix_def)
  have rest_len: "length rest \<le> length (drop k bs)"
    by (rule varint_decode_length[OF dec])
  have k_le: "k < length bs"
  proof (rule ccontr)
    assume "\<not> k < length bs"
    hence "drop k bs = []" by simp
    hence "varint_decode (drop k bs) = None"
      by (simp add: varint_decode_def numeral_nat)
    with dec show False by simp
  qed
  have dk_len: "length (drop k bs) = length pfx + length rest"
    using eq by simp
  have pfx_len: "length pfx = length bs - k - length rest"
    using dk_len k_le by simp
  have "rest = drop (length pfx) (drop k bs)"
    using eq by simp
  also have "\<dots> = drop (k + length pfx) bs"
    by (simp add: drop_drop add.commute)
  also have "k + length pfx = length bs - length rest"
    using pfx_len k_le rest_len by simp
  finally show ?thesis by simp
qed

(*
  After a varint decode from position pos in the buffer, the next varint
  can be decoded from the remaining bytes. This connects the position arithmetic.
*)
lemma varint_next_position:
  assumes dec: "varint_decode (drop (unat pos) (heap_bytes s buf (unat (len :: 32 word)))) = Some (v, rest)"
      and rest_le: "length rest \<le> unat len - unat (pos :: 32 word)"
      and rest_lt: "length rest < 2 ^ 32"
      and pos_le: "unat pos \<le> unat len"
  shows "drop (unat (len - of_nat (length rest) :: 32 word))
              (heap_bytes s buf (unat len)) = rest"
proof -
  have unat_rest: "unat (of_nat (length rest) :: 32 word) = length rest"
    using rest_lt by (simp add: unat_of_nat_eq)
  have rest_le_len: "(of_nat (length rest) :: 32 word) \<le> len"
    using rest_le unat_rest by (simp add: word_le_nat_alt)
  have "unat (len - of_nat (length rest) :: 32 word) = unat len - length rest"
    using rest_le_len unat_rest by (simp add: unat_sub)
  thus ?thesis
    using varint_decode_drop_rest[OF dec] pos_le
    by simp
qed

(* ---------- Pointer arithmetic helpers ---------- *)

(*
  Pointer offset injectivity: if two offsets are different within the valid
  range (< 2^32 for 32-bit pointers), the resulting pointers differ.
*)
lemma ptr_add_inject:
  assumes "i \<noteq> j" "0 \<le> i" "i < 2 ^ 32" "0 \<le> j" "j < 2 ^ 32"
  shows "(p :: 8 word ptr) +\<^sub>p i \<noteq> p +\<^sub>p j"
proof
  assume eq: "p +\<^sub>p i = p +\<^sub>p j"
  hence "ptr_val p + word_of_int i = ptr_val p + word_of_int j"
    by (simp add: ptr_add_def)
  hence weq: "word_of_int i = (word_of_int j :: addr)" by simp
  have "uint (word_of_int i :: addr) = uint (word_of_int j :: addr)"
    using weq by simp
  hence "i mod 2 ^ 32 = j mod 2 ^ 32"
    by (simp add: uint_word_of_int)
  hence "i = j" using assms(2,3,4,5) by simp
  with assms(1) show False by simp
qed

lemma ptr_add_inject_nat:
  assumes "i \<noteq> j" "i < 2 ^ 32" "j < 2 ^ 32"
  shows "(p :: 8 word ptr) +\<^sub>p int i \<noteq> p +\<^sub>p int j"
  using assms by (intro ptr_add_inject) simp_all

(* ---------- Phase 3: Main loop instruction lemmas ---------- *)

(*
  ADD instruction inner loop: copies sz bytes from patch[data_cursor..]
  to out[tgt_pos..]. Proves that the resulting heap_bytes of the output
  region matches the original output appended with the source bytes.

  Preconditions:
    - Source bytes readable: buf_valid for patch at the relevant range
    - Output bytes writable: buf_valid for out at the relevant range
    - Disjoint: writes to out don't affect reads from patch
    - No overflow in pointer arithmetic

  Postcondition:
    - heap_bytes t out (unat tgt_pos + unat sz) =
        heap_bytes s out (unat tgt_pos) @
        take (unat sz) (drop (unat data_cursor) (heap_bytes s patch patch_n))
    - data_cursor and tgt_pos advanced by sz
    - patch heap_bytes unchanged
*)
lemma add_loop_correct:
  fixes sz :: "32 word" and data_cursor :: "32 word"
    and tgt_pos :: "32 word" and patch :: "8 word ptr" and out :: "8 word ptr"
  assumes sz_pos: "0 < unat sz"
      and data_valid: "\<forall>j < unat sz.
           ptr_valid (heap_typing s) (patch +\<^sub>p uint (data_cursor + of_nat j))"
      and out_valid: "\<forall>j < unat sz.
           ptr_valid (heap_typing s) (out +\<^sub>p uint (tgt_pos + of_nat j))"
      and disj: "\<forall>i < unat sz. \<forall>j < patch_n.
           out +\<^sub>p uint (tgt_pos + of_nat i) \<noteq> patch +\<^sub>p int j"
      and out_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
           i \<noteq> j \<longrightarrow> out +\<^sub>p uint (tgt_pos + of_nat i) \<noteq> out +\<^sub>p uint (tgt_pos + of_nat j)"
      and no_overflow_data: "unat data_cursor + unat sz < 2 ^ 32"
      and no_overflow_tgt: "unat tgt_pos + unat sz < 2 ^ 32"
      and data_in_range: "unat data_cursor + unat sz \<le> patch_n"
  shows "(whileLoop (\<lambda>(j :: 32 word) st. j < sz)
           (\<lambda>j. do {
              guard (\<lambda>st. ptr_valid (heap_typing st) (patch +\<^sub>p uint (data_cursor + j)));
              b \<leftarrow> gets (\<lambda>st. heap_w8 st (patch +\<^sub>p uint (data_cursor + j)));
              guard (\<lambda>st. ptr_valid (heap_typing st) (out +\<^sub>p uint (tgt_pos + j)));
              modify (heap_w8_update (\<lambda>h. h(out +\<^sub>p uint (tgt_pos + j) := b)));
              return (j + 1)
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result sz \<and>
            (\<forall>j < patch_n. heap_w8 t (patch +\<^sub>p int j) = heap_w8 s (patch +\<^sub>p int j)) \<and>
            (\<forall>j < unat sz. heap_w8 t (out +\<^sub>p uint (tgt_pos + of_nat j)) =
               heap_w8 s (patch +\<^sub>p uint (data_cursor + of_nat j))) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((j :: 32 word), _). unat sz - unat j)"
      and I = "\<lambda>j st. unat j \<le> unat sz
             \<and> (\<forall>k < patch_n. heap_w8 st (patch +\<^sub>p int k) = heap_w8 s (patch +\<^sub>p int k))
             \<and> (\<forall>k < unat j. heap_w8 st (out +\<^sub>p uint (tgt_pos + of_nat k)) =
                  heap_w8 s (patch +\<^sub>p uint (data_cursor + of_nat k)))
             \<and> heap_typing st = heap_typing s"])
     subgoal by simp
    subgoal by (simp add: word_less_nat_alt)
   subgoal for j st
     by (clarsimp simp: word_less_nat_alt)
  subgoal for j st
    apply runs_to_vcg
    \<comment> \<open>1. Guard: ptr_valid for patch read\<close>
           subgoal
             using data_valid[rule_format, of "unat j"]
             by (simp add: word_less_nat_alt word_unat.Rep_inverse)
    \<comment> \<open>2. Guard: ptr_valid for out write\<close>
          subgoal
            using out_valid[rule_format, of "unat j"]
            by (simp add: word_less_nat_alt word_unat.Rep_inverse)
    \<comment> \<open>3. Bound: unat (j + 1) \<le> unat sz\<close>
         subgoal using no_overflow_tgt by unat_arith

    \<comment> \<open>4. Patch preservation (equal ptr case - impossible by disj)\<close>
        subgoal for k
          using disj[rule_format, of "unat j" k]
          by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
    \<comment> \<open>5. Patch preservation (not-equal): direct from IH\<close>
       subgoal by auto
    \<comment> \<open>6. Output (equal ptr case): k = unat j, value from patch\<close>
      subgoal for k
        apply (subgoal_tac "k = unat j")
         apply (clarsimp simp: word_unat.Rep_inverse)
         apply (subgoal_tac "unat (data_cursor + j) < patch_n")
          apply (simp only: uint_nat)
         using data_in_range no_overflow_data
         apply (subgoal_tac "unat (data_cursor + j) = unat data_cursor + unat j")
          apply (simp add: word_less_nat_alt)
         apply (simp only: unat_add_lem[symmetric])
         apply (simp add: word_less_nat_alt)
        apply (simp add: ptr_add_def word_of_int_uint)
        apply (drule unat_cong)
        apply (simp only: unat_of_nat)
        apply (subgoal_tac "k < 2 ^ LENGTH(32)")
         apply simp
        using less_trans unsigned_less[where w="j + 1 :: 32 word" and 'b=32]
        by simp
    \<comment> \<open>7. Output (not-equal ptr case): k < unat j, from IH\<close>
     subgoal for k
       apply (subgoal_tac "k < unat j")
        apply auto[1]
       apply (cases "k = unat j")
        apply (simp add: word_unat.Rep_inverse)
       using no_overflow_tgt by unat_arith
    \<comment> \<open>8. Termination measure\<close>
    subgoal using no_overflow_tgt by unat_arith
    done
  done

(*
  RUN instruction inner loop: fills sz bytes of out[tgt_pos..] with
  a single byte `fill`. Simpler than ADD since the source is a constant.

  Postcondition:
    - All output bytes in [tgt_pos, tgt_pos + sz) equal fill
    - patch heap unchanged
*)
lemma run_loop_correct:
  fixes sz :: "32 word" and tgt_pos :: "32 word"
    and fill :: "8 word" and out :: "8 word ptr"
  assumes sz_pos: "0 < unat sz"
      and out_valid: "\<forall>j < unat sz.
           ptr_valid (heap_typing s) (out +\<^sub>p uint (tgt_pos + of_nat j))"
      and disj: "\<forall>i < unat sz. \<forall>j < patch_n.
           out +\<^sub>p uint (tgt_pos + of_nat i) \<noteq> patch +\<^sub>p int j"
      and out_inj: "\<forall>i < unat sz. \<forall>j < unat sz.
           i \<noteq> j \<longrightarrow> out +\<^sub>p uint (tgt_pos + of_nat i) \<noteq> out +\<^sub>p uint (tgt_pos + of_nat j)"
      and no_overflow_tgt: "unat tgt_pos + unat sz < 2 ^ 32"
  shows "(whileLoop (\<lambda>(j :: 32 word) st. j < sz)
           (\<lambda>j. do {
              guard (\<lambda>st. ptr_valid (heap_typing st) (out +\<^sub>p uint (tgt_pos + j)));
              modify (heap_w8_update (\<lambda>h. h(out +\<^sub>p uint (tgt_pos + j) := fill)));
              return (j + 1)
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result sz \<and>
            (\<forall>j < patch_n. heap_w8 t (patch +\<^sub>p int j) = heap_w8 s (patch +\<^sub>p int j)) \<and>
            (\<forall>j < unat sz. heap_w8 t (out +\<^sub>p uint (tgt_pos + of_nat j)) = fill) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((j :: 32 word), _). unat sz - unat j)"
      and I = "\<lambda>j st. unat j \<le> unat sz
             \<and> (\<forall>k < patch_n. heap_w8 st (patch +\<^sub>p int k) = heap_w8 s (patch +\<^sub>p int k))
             \<and> (\<forall>k < unat j. heap_w8 st (out +\<^sub>p uint (tgt_pos + of_nat k)) = fill)
             \<and> heap_typing st = heap_typing s"])
     subgoal by simp
    subgoal by (simp add: word_less_nat_alt)
   subgoal for j st
     by (clarsimp simp: word_less_nat_alt)
  subgoal for j st
    apply runs_to_vcg
    \<comment> \<open>1. Guard: ptr_valid for out write\<close>
        subgoal
          using out_valid[rule_format, of "unat j"]
          by (simp add: word_less_nat_alt word_unat.Rep_inverse)
    \<comment> \<open>2. Bound: unat (j+1) \<le> unat sz\<close>
       subgoal using no_overflow_tgt by unat_arith
    \<comment> \<open>3. Patch preservation (equal ptr - impossible by disj)\<close>
      subgoal for k
        using disj[rule_format, of "unat j" k]
        by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
    \<comment> \<open>4. Patch preservation (not-equal - trivial from IH)\<close>
     subgoal by auto
    \<comment> \<open>5. Output correct (not-equal ptr): k < unat j from IH\<close>
    subgoal for k
      apply (subgoal_tac "k < unat j")
       apply auto[1]
      apply (cases "k = unat j")
       apply (simp add: word_unat.Rep_inverse)
      using no_overflow_tgt by unat_arith
   \<comment> \<open>6. Termination measure\<close>
    subgoal using no_overflow_tgt by unat_arith
    done
  done

(*
  COPY instruction inner loop: copies sz bytes where each source byte
  comes from either src[src_seg_off + a] (if a < src_seg_len) or
  out[a - src_seg_len] (overlapping copy from already-written output).

  The loop invariant tracks:
  - Patch/src heaps unchanged (writes only go to out[tgt_pos..])
  - Output bytes written so far match copy_loop semantics
  - heap_typing preserved

  This is the hardest instruction because the source for each byte can
  be a previously-written output byte (overlapping copy).
*)

(* copy_loop preserves the prefix *)
lemma copy_loop_prefix:
  "i < length tgt \<Longrightarrow> copy_loop src tgt addr n ! i = tgt ! i"
  by (induct n arbitrary: tgt addr) (simp_all add: nth_append)

(* Helper: copy_loop_nth characterization for indexing into the result *)
lemma copy_loop_nth:
  assumes "k < n"
  shows "copy_loop src tgt addr n ! (length tgt + k) =
         combined_byte src (copy_loop src tgt addr k) (addr + k)"
  using assms
proof (induct k arbitrary: tgt addr n)
  case 0
  then obtain n' where n_eq: "n = Suc n'" by (cases n) simp_all
  show ?case
    unfolding n_eq by (simp add: copy_loop_prefix nth_append)
next
  case (Suc k)
  then obtain n' where n_eq: "n = Suc n'" by (cases n) simp_all
  have step: "copy_loop src tgt addr (Suc n') =
              copy_loop src (tgt @ [combined_byte src tgt addr]) (addr + 1) n'"
    by simp
  have "copy_loop src tgt addr (Suc n') ! (length tgt + Suc k)
      = copy_loop src (tgt @ [combined_byte src tgt addr]) (addr + 1) n'
        ! (length (tgt @ [combined_byte src tgt addr]) + k)"
    by simp
  also have "\<dots> = combined_byte src
                    (copy_loop src (tgt @ [combined_byte src tgt addr]) (addr + 1) k)
                    (addr + 1 + k)"
    using Suc.hyps[where tgt="tgt @ [combined_byte src tgt addr]"
                     and addr="addr + 1" and n=n']
          Suc.prems n_eq by simp
  also have "addr + 1 + k = addr + Suc k" by simp
  finally show ?case using n_eq by simp
qed

lemma copy_loop_nth_stable:
  assumes "k < n"
  shows "copy_loop src tgt addr (Suc n) ! (length tgt + k) =
         copy_loop src tgt addr n ! (length tgt + k)"
  using copy_loop_nth[OF assms] copy_loop_nth[of k "Suc n" src tgt addr]
        assms by simp

lemma copy_loop_nth_src:
  assumes "addr + j < length src"
  shows "copy_loop src tgt addr (Suc j) ! (length tgt + j) = src ! (addr + j)"
  using copy_loop_nth[of j "Suc j" src tgt addr]
  by (simp add: combined_byte_def assms)

lemma copy_loop_nth_tgt:
  assumes "\<not> (addr + j < length src)"
  shows "copy_loop src tgt addr (Suc j) ! (length tgt + j) =
         copy_loop src tgt addr j ! (addr + j - length src)"
  using copy_loop_nth[of j "Suc j" src tgt addr]
  by (simp add: combined_byte_def assms)

lemma unat_add_no_overflow:
  fixes a b :: "32 word"
  assumes "unat a + unat b < 2 ^ 32"
  shows "unat (a + b) = unat a + unat b"
  using assms unat_add_lem[of a b] by simp

lemma copy_loop_overlap_ptr_eq:
  fixes addr j src_seg_len tgt_pos :: "32 word"
  assumes addr_j: "unat (addr + j) = unat addr + unat j"
      and ge: "\<not> addr + j < src_seg_len"
      and ge_tgt: "\<not> unat addr + unat j - unat src_seg_len < unat tgt_pos"
      and no_ovf: "unat tgt_pos + (unat addr + unat j - unat src_seg_len - unat tgt_pos) < 2 ^ 32"
  shows "addr + j - src_seg_len =
         tgt_pos + word_of_nat (unat addr + unat j - unat src_seg_len - unat tgt_pos)"
proof -
  have le: "src_seg_len \<le> addr + j" using ge by (simp add: linorder_not_less)
  have unat_sub_eq: "unat (addr + j - src_seg_len) = unat addr + unat j - unat src_seg_len"
    using addr_j le by (simp add: unat_sub word_le_nat_alt)
  let ?m = "unat addr + unat j - unat src_seg_len - unat tgt_pos"
  have m_bound: "?m < 2 ^ 32"
    using no_ovf by linarith
  have unat_wm: "unat (word_of_nat ?m :: 32 word) = ?m"
    using m_bound by (simp add: unat_of_nat_eq)
  have no_ovf': "unat tgt_pos + unat (word_of_nat ?m :: 32 word) < 2 ^ 32"
    using no_ovf unat_wm by simp
  have unat_rhs: "unat (tgt_pos + word_of_nat ?m :: 32 word) = unat tgt_pos + ?m"
    using unat_add_no_overflow[OF no_ovf'] unat_wm by simp
  have eq: "unat addr + unat j - unat src_seg_len = unat tgt_pos + ?m"
    using ge_tgt by linarith
  have "unat (addr + j - src_seg_len) = unat (tgt_pos + word_of_nat ?m :: 32 word)"
    using unat_sub_eq unat_rhs eq by linarith
  thus ?thesis by (rule word_unat.Rep_inject[THEN iffD1])
qed

lemma heap_bytes_nth_ptr:
  fixes off :: "32 word" and i j :: "32 word"
  assumes seg_def: "src_seg = heap_bytes s (src +\<^sub>p uint off) (unat len)"
      and idx_bound: "unat i + unat j < unat len"
      and no_ovf: "unat off + (unat i + unat j) < 2 ^ 32"
  shows "heap_w8 s (src +\<^sub>p uint (off + (i + j))) = src_seg ! (unat i + unat j)"
proof -
  have nth: "src_seg ! (unat i + unat j) = heap_w8 s (src +\<^sub>p uint off +\<^sub>p int (unat i + unat j))"
    using seg_def idx_bound by (simp add: heap_bytes_nth)
  have ij_no_ovf: "unat i + unat j < 2 ^ 32"
    using idx_bound no_ovf by linarith
  have uij: "unat (i + j) = unat i + unat j"
    using ij_no_ovf unat_add_lem[of i j] by simp
  have oij: "unat (off + (i + j)) = unat off + (unat i + unat j)"
    using no_ovf uij unat_add_lem[of off "i + j"] by simp
  have "src +\<^sub>p uint (off + (i + j)) = src +\<^sub>p uint off +\<^sub>p int (unat i + unat j)"
    unfolding ptr_add_def uint_nat oij of_int_of_nat_eq by simp
  thus ?thesis using nth by simp
qed

lemma ptr_add_uint_eq:
  "(p :: 8 word ptr) +\<^sub>p uint (x :: 32 word) = p +\<^sub>p uint (y :: 32 word) \<Longrightarrow> x = y"
proof -
  assume "p +\<^sub>p uint x = p +\<^sub>p uint y"
  hence "ptr_val p + word_of_int (uint x) = ptr_val p + word_of_int (uint y)"
    by (simp add: ptr_add_def)
  hence "word_of_int (uint x) = (word_of_int (uint y) :: addr)" by simp
  hence "uint (word_of_int (uint x) :: addr) = uint (word_of_int (uint y) :: addr)"
    by simp
  hence "uint x mod 2 ^ 32 = uint y mod 2 ^ 32"
    by (simp add: uint_word_of_int)
  moreover have "0 \<le> uint x" "uint x < 2 ^ 32"
    using uint_ge_0[of x] uint_lt2p[of x] by simp_all
  moreover have "0 \<le> uint y" "uint y < 2 ^ 32"
    using uint_ge_0[of y] uint_lt2p[of y] by simp_all
  ultimately have "uint x = uint y" by simp
  thus "x = y" by (simp add: word_uint.Rep_inject)
qed

lemma copy_out_eq_idx:
  assumes "(out :: 8 word ptr) +\<^sub>p uint (tgt_pos + word_of_nat k) =
           out +\<^sub>p uint (tgt_pos + (j :: 32 word))"
      and "k < 2 ^ LENGTH(32)"
  shows "k = unat j"
proof -
  from assms(1) have eq: "tgt_pos + (word_of_nat k :: 32 word) = tgt_pos + j"
    by (rule ptr_add_uint_eq)
  hence "(word_of_nat k :: 32 word) = j" by simp
  hence "unat (word_of_nat k :: 32 word) = unat j" by simp
  moreover have "unat (word_of_nat k :: 32 word) = k"
    using assms(2) by (simp add: unat_of_nat_eq)
  ultimately show "k = unat j" by simp
qed

(*
  COPY instruction inner loop correctness.

  The loop copies sz bytes to out[tgt_pos..], where each byte comes from either:
  - src[src_seg_off + addr + j] when addr + j < src_seg_len (source segment)
  - out[addr + j - src_seg_len] when addr + j >= src_seg_len (overlapping copy)

  Invariant: after j iterations, the bytes written match copy_loop's output.

  Key parameters:
  - src_seg: the source segment bytes = heap_bytes s src src_seg_len (at offset src_seg_off)
  - tgt_pre: the output bytes before this COPY = heap_bytes s out (unat tgt_pos)
  - addr_nat: natural number address for copy_loop = unat addr
*)
lemma copy_loop_correct:
  fixes sz :: "32 word" and tgt_pos :: "32 word"
    and addr :: "32 word" and src_seg_len :: "32 word" and src_seg_off :: "32 word"
    and src :: "8 word ptr" and out :: "8 word ptr"
    and src_seg :: "8 word list" and tgt_pre :: "8 word list"
  assumes src_seg_def: "src_seg = heap_bytes s (src +\<^sub>p uint src_seg_off) (unat src_seg_len)"
      and tgt_pre_def: "tgt_pre = heap_bytes s out (unat tgt_pos)"
      and sz_pos: "0 < unat sz"
      and src_valid: "\<forall>j < unat sz.
           unat (addr + of_nat j) < unat src_seg_len \<longrightarrow>
           ptr_valid (heap_typing s)
             (src +\<^sub>p uint (src_seg_off + addr + of_nat j))"
      and out_read_valid: "\<forall>j < unat sz.
           \<not> (addr + of_nat j < src_seg_len) \<longrightarrow>
           ptr_valid (heap_typing s)
             (out +\<^sub>p uint (addr + of_nat j - src_seg_len))"
      and out_write_valid: "\<forall>j < unat sz.
           ptr_valid (heap_typing s) (out +\<^sub>p uint (tgt_pos + of_nat j))"
      and disj_src_out: "\<forall>i < unat sz. \<forall>j < src_n.
           out +\<^sub>p uint (tgt_pos + of_nat i) \<noteq> src +\<^sub>p int j"
      and disj_patch_out: "\<forall>i < unat sz. \<forall>j < patch_n.
           out +\<^sub>p uint (tgt_pos + of_nat i) \<noteq> patch +\<^sub>p int j"
      and out_inj: "\<forall>i < unat tgt_pos + unat sz. \<forall>j < unat tgt_pos + unat sz.
           i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j"
      and no_overflow_tgt: "unat tgt_pos + unat sz < 2 ^ 32"
      and no_overflow_combined: "unat src_seg_len + unat tgt_pos + unat sz < 2 ^ 32"
      and no_overflow_addr: "unat addr + unat sz \<le> unat src_seg_len + unat tgt_pos + unat sz"
      and addr_bound: "unat addr < unat src_seg_len + unat tgt_pos"
      and no_overflow_src_seg: "unat src_seg_off + unat src_seg_len < 2 ^ 32"
      and src_seg_in_range: "unat src_seg_off + unat src_seg_len \<le> src_n"
  shows "(whileLoop (\<lambda>(j :: 32 word) st. j < sz)
           (\<lambda>j. do {
              let a = addr + j;
              (if a < src_seg_len then do {
                 guard (\<lambda>st. ptr_valid (heap_typing st) (src +\<^sub>p uint (src_seg_off + a)));
                 b \<leftarrow> gets (\<lambda>st. heap_w8 st (src +\<^sub>p uint (src_seg_off + a)));
                 guard (\<lambda>st. ptr_valid (heap_typing st) (out +\<^sub>p uint (tgt_pos + j)));
                 modify (heap_w8_update (\<lambda>h. h(out +\<^sub>p uint (tgt_pos + j) := b)));
                 return (j + 1)
               } else do {
                 let tgt_rel = a - src_seg_len;
                 guard (\<lambda>st. ptr_valid (heap_typing st) (out +\<^sub>p uint tgt_rel));
                 b \<leftarrow> gets (\<lambda>st. heap_w8 st (out +\<^sub>p uint tgt_rel));
                 guard (\<lambda>st. ptr_valid (heap_typing st) (out +\<^sub>p uint (tgt_pos + j)));
                 modify (heap_w8_update (\<lambda>h. h(out +\<^sub>p uint (tgt_pos + j) := b)));
                 return (j + 1)
               })
           }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s
         \<lbrace> \<lambda>r t. r = Result sz \<and>
            (\<forall>j < patch_n. heap_w8 t (patch +\<^sub>p int j) = heap_w8 s (patch +\<^sub>p int j)) \<and>
            (\<forall>j < src_n. heap_w8 t (src +\<^sub>p int j) = heap_w8 s (src +\<^sub>p int j)) \<and>
            (\<forall>k < unat sz.
               heap_w8 t (out +\<^sub>p uint (tgt_pos + of_nat k)) =
               copy_loop src_seg tgt_pre (unat addr) (unat sz)
                 ! (unat tgt_pos + k)) \<and>
            heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
    where R = "measure (\<lambda>((j :: 32 word), _). unat sz - unat j)"
      and I = "\<lambda>j st. unat j \<le> unat sz
             \<and> (\<forall>k < patch_n. heap_w8 st (patch +\<^sub>p int k) = heap_w8 s (patch +\<^sub>p int k))
             \<and> (\<forall>k < src_n. heap_w8 st (src +\<^sub>p int k) = heap_w8 s (src +\<^sub>p int k))
             \<and> (\<forall>k < unat j.
                  heap_w8 st (out +\<^sub>p uint (tgt_pos + of_nat k)) =
                  copy_loop src_seg tgt_pre (unat addr) (unat j)
                    ! (unat tgt_pos + k))
             \<and> (\<forall>i < unat tgt_pos.
                  heap_w8 st (out +\<^sub>p int i) = heap_w8 s (out +\<^sub>p int i))
             \<and> heap_typing st = heap_typing s"])
     subgoal by simp
    subgoal by (simp add: word_less_nat_alt)
   subgoal for j st
     by (clarsimp simp: word_less_nat_alt)
  subgoal for j st
    apply (clarsimp simp: Let_def)
    apply (cases "addr + j < src_seg_len")
    subgoal \<comment> \<open>Source branch: read from src[src_seg_off + addr + j]\<close>
      apply simp
      apply runs_to_vcg
      \<comment> \<open>1. src guard\<close>
             subgoal using src_valid[rule_format, of "unat j"]
               by (simp add: word_less_nat_alt word_unat.Rep_inverse ac_simps)
      \<comment> \<open>2. out guard\<close>
            subgoal using out_write_valid[rule_format, of "unat j"]
              by (simp add: word_less_nat_alt word_unat.Rep_inverse)
      \<comment> \<open>3. bound\<close>
           subgoal using no_overflow_tgt by unat_arith
      \<comment> \<open>4. patch preservation (eq ptr - impossible)\<close>
          subgoal for k
            using disj_patch_out[rule_format, of "unat j" k]
            by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
      \<comment> \<open>5. patch preservation (neq)\<close>
         subgoal by auto
      \<comment> \<open>6. src preservation (eq ptr - impossible)\<close>
        subgoal for k
          using disj_src_out[rule_format, of "unat j" k]
          by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
      \<comment> \<open>7. src preservation (neq)\<close>
       subgoal by auto
      \<comment> \<open>8. output correctness (eq ptr) — source branch\<close>
      subgoal for k
        apply (subgoal_tac "k = unat j")
         prefer 2
         apply (rule copy_out_eq_idx, assumption)
         apply (erule less_trans, rule unsigned_less)
        apply (simp only:)
        \<comment> \<open>Goal: heap_w8 st (src +p ...) = copy_loop ... ! (...)\<close>
        \<comment> \<open>Strategy: chain equalities via subgoal_tacs, then prove obligations\<close>
        apply (subgoal_tac "heap_w8 st (src +\<^sub>p uint (src_seg_off + (addr + j))) =
                 heap_w8 s (src +\<^sub>p uint (src_seg_off + (addr + j)))")
         apply (subgoal_tac "heap_w8 s (src +\<^sub>p uint (src_seg_off + (addr + j))) =
                  src_seg ! (unat addr + unat j)")
          apply (subgoal_tac "copy_loop src_seg tgt_pre (unat addr) (unat (j + 1))
                   ! (unat tgt_pos + unat j) = src_seg ! (unat addr + unat j)")
           apply simp
          \<comment> \<open>Prove: copy_loop ... = src_seg ! ...\<close>
          apply (subgoal_tac "unat (j + 1) = Suc (unat j)")
           apply (subgoal_tac "unat tgt_pos = length tgt_pre")
            apply (subgoal_tac "unat addr + unat j < length src_seg")
             apply (simp only: copy_loop_nth_src)
            apply (subgoal_tac "unat (addr + j) = unat addr + unat j")
             apply (subgoal_tac "length src_seg = unat src_seg_len")
              apply (simp only: word_less_nat_alt)
             using src_seg_def apply (simp add: heap_bytes_def)
            apply (rule unat_add_no_overflow)
            using no_overflow_combined no_overflow_addr apply linarith
           using tgt_pre_def apply (simp add: heap_bytes_def)
          using no_overflow_tgt apply unat_arith
         \<comment> \<open>Prove: heap_w8 s ... = src_seg ! ...\<close>
         apply (rule heap_bytes_nth_ptr[OF src_seg_def])
          apply (subgoal_tac "unat (addr + j) = unat addr + unat j")
           apply (simp only: word_less_nat_alt)
          apply (rule unat_add_no_overflow)
          using no_overflow_combined no_overflow_addr apply linarith
         apply (subgoal_tac "unat addr + unat j < unat src_seg_len")
          using no_overflow_src_seg apply linarith
         apply (subgoal_tac "unat (addr + j) = unat addr + unat j")
          apply (simp only: word_less_nat_alt)
         apply (rule unat_add_no_overflow)
         using no_overflow_combined no_overflow_addr apply linarith
        \<comment> \<open>Prove: heap_w8 st ... = heap_w8 s ...\<close>
        apply (subgoal_tac "unat (addr + j) = unat addr + unat j")
         prefer 2
         apply (rule unat_add_no_overflow)
         using no_overflow_combined no_overflow_addr apply linarith
        apply (subgoal_tac "unat (addr + j) < unat src_seg_len")
         prefer 2
         apply (metis word_less_nat_alt)
        apply (subgoal_tac "unat (src_seg_off + (addr + j)) = unat src_seg_off + unat (addr + j)")
         prefer 2
         apply (rule unat_add_no_overflow)
         using no_overflow_src_seg apply linarith
        apply (subgoal_tac "unat (src_seg_off + (addr + j)) < src_n")
         prefer 2
         using src_seg_in_range apply linarith
        apply (simp only: uint_nat)
        done
      \<comment> \<open>9. output correctness (neq ptr)\<close>
      subgoal for k
        apply (subgoal_tac "k < unat j")
         apply (subgoal_tac "copy_loop src_seg tgt_pre (unat addr) (unat (j + 1))
                  ! (unat tgt_pos + k) =
                copy_loop src_seg tgt_pre (unat addr) (unat j)
                  ! (unat tgt_pos + k)")
          apply simp
         apply (subgoal_tac "unat (j + 1) = Suc (unat j)")
          apply (subgoal_tac "unat tgt_pos = length tgt_pre")
           apply (simp only:)
           apply (rule copy_loop_nth_stable)
           apply assumption
          using tgt_pre_def apply simp
         using no_overflow_tgt apply unat_arith
        apply (cases "k = unat j")
         apply (simp add: word_unat.Rep_inverse)
        apply (subgoal_tac "unat (j + 1 :: 32 word) = unat j + 1")
         apply linarith
        using no_overflow_tgt by unat_arith
      \<comment> \<open>10. prefix preservation (eq ptr - impossible)\<close>
      subgoal for i
        apply (subgoal_tac "out +\<^sub>p int (unat tgt_pos + unat j) = out +\<^sub>p uint (tgt_pos + j)")
         using out_inj[rule_format, of i "unat tgt_pos + unat j"]
         apply (simp add: word_less_nat_alt)
        apply (subgoal_tac "unat (tgt_pos + j) = unat tgt_pos + unat j")
         apply (simp only: ptr_add_def uint_nat of_int_of_nat_eq)
        apply (rule iffD1[OF unat_add_lem])
        using no_overflow_tgt by (auto simp: word_less_nat_alt)
      \<comment> \<open>11. prefix preservation (neq ptr)\<close>
      subgoal by simp
      \<comment> \<open>12. termination\<close>
      subgoal
        apply (subgoal_tac "unat (j + 1 :: 32 word) = unat j + 1")
         apply (subgoal_tac "unat j < unat sz")
          apply linarith
         apply (simp only: word_less_nat_alt)
        using no_overflow_tgt by unat_arith
      done
    subgoal \<comment> \<open>Overlapping copy branch: read from out[addr + j - src_seg_len]\<close>
      apply simp
      apply runs_to_vcg
      \<comment> \<open>1. out read guard\<close>
             subgoal using out_read_valid[rule_format, of "unat j"]
               by (simp add: word_less_nat_alt word_unat.Rep_inverse unat_sub)
      \<comment> \<open>2. out write guard\<close>
            subgoal using out_write_valid[rule_format, of "unat j"]
              by (simp add: word_less_nat_alt word_unat.Rep_inverse)
      \<comment> \<open>3. bound\<close>
           subgoal using no_overflow_tgt by unat_arith
      \<comment> \<open>4. patch preservation (eq ptr - impossible)\<close>
          subgoal for k
            using disj_patch_out[rule_format, of "unat j" k]
            by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
      \<comment> \<open>5. patch preservation (neq)\<close>
         subgoal by auto
      \<comment> \<open>6. src preservation (eq ptr - impossible)\<close>
        subgoal for k
          using disj_src_out[rule_format, of "unat j" k]
          by (auto simp: word_less_nat_alt word_unat.Rep_inverse)
      \<comment> \<open>7. src preservation (neq)\<close>
       subgoal by auto
      \<comment> \<open>8. output correctness (eq ptr) — overlapping branch\<close>
      subgoal for k
        apply (subgoal_tac "k = unat j")
         prefer 2
         apply (rule copy_out_eq_idx, assumption)
         apply (erule less_trans, rule unsigned_less)
        apply (simp only:)
        \<comment> \<open>RHS: copy_loop ... (unat (j+1)) ! (unat tgt_pos + unat j)\<close>
        \<comment> \<open>Reduce via copy_loop_nth_tgt\<close>
        apply (subgoal_tac "unat (j + 1) = Suc (unat j)")
         prefer 2
         using no_overflow_tgt apply unat_arith
        apply (subgoal_tac "unat tgt_pos = length tgt_pre")
         prefer 2
         using tgt_pre_def apply (simp add: heap_bytes_def)
        apply (subgoal_tac "length src_seg = unat src_seg_len")
         prefer 2
         using src_seg_def apply (simp add: heap_bytes_def)
        apply (subgoal_tac "unat (addr + j) = unat addr + unat j")
         prefer 2
         apply (rule unat_add_no_overflow)
         using no_overflow_combined no_overflow_addr apply linarith
        apply (subgoal_tac "\<not> (unat addr + unat j < length src_seg)")
         prefer 2
         apply (metis word_less_nat_alt)
        apply (subgoal_tac "copy_loop src_seg tgt_pre (unat addr) (Suc (unat j))
                 ! (length tgt_pre + unat j) =
               copy_loop src_seg tgt_pre (unat addr) (unat j)
                 ! (unat addr + unat j - length src_seg)")
         prefer 2
         apply (rule copy_loop_nth_tgt)
         apply linarith
        \<comment> \<open>Now goal reduces to: heap_w8 st (out +p uint (addr+j-src_seg_len)) =
              copy_loop src_seg tgt_pre (unat addr) (unat j) ! (unat addr + unat j - length src_seg)\<close>
        apply (simp only:)
        \<comment> \<open>Case split: is the read address in prefix or loop-written region?\<close>
        apply (cases "unat addr + unat j - unat src_seg_len < unat tgt_pos")
        \<comment> \<open>Case A: prefix region — use prefix invariant + tgt_pre\<close>
         apply (subgoal_tac "copy_loop src_seg tgt_pre (unat addr) (unat j)
                  ! (unat addr + unat j - length src_seg) =
                tgt_pre ! (unat addr + unat j - length src_seg)")
          prefer 2
          apply (rule copy_loop_prefix)
          apply linarith
         apply (simp only:)
         apply (subgoal_tac "tgt_pre ! (unat addr + unat j - length src_seg) =
                  heap_w8 s (out +\<^sub>p int (unat addr + unat j - unat src_seg_len))")
          prefer 2
          apply (subst tgt_pre_def)
          apply (subst heap_bytes_nth)
           apply linarith
          apply simp
         apply (simp only:)
         apply (subgoal_tac "heap_w8 st (out +\<^sub>p uint (addr + j - src_seg_len)) =
                  heap_w8 st (out +\<^sub>p int (unat addr + unat j - unat src_seg_len))")
          prefer 2
          apply (subgoal_tac "src_seg_len \<le> addr + j")
           prefer 2
           apply (simp add: linorder_not_less)
          apply (subgoal_tac "unat (addr + j - src_seg_len) = unat addr + unat j - unat src_seg_len")
           apply (simp only: ptr_add_def uint_nat of_int_of_nat_eq)
          apply (simp add: unat_sub word_le_nat_alt)
         apply (simp only:)
         apply (simp only: uint_nat)
        \<comment> \<open>Case B: loop-written region — use output invariant + ptr equality\<close>
        apply (subgoal_tac "addr + j - src_seg_len =
               tgt_pos + word_of_nat (unat addr + unat j - unat src_seg_len - unat tgt_pos)")
         prefer 2
         apply (rule copy_loop_overlap_ptr_eq)
            apply assumption
           apply assumption
          apply linarith
         using no_overflow_combined no_overflow_addr apply linarith
        apply (subgoal_tac "unat addr + unat j - unat src_seg_len - unat tgt_pos < unat j")
         prefer 2
         using addr_bound apply linarith
        apply (subgoal_tac "unat addr + unat j - unat src_seg_len =
               unat tgt_pos + (unat addr + unat j - unat src_seg_len - unat tgt_pos)")
         prefer 2
         apply linarith
        apply (simp only: uint_nat)
        done
      \<comment> \<open>9. output correctness (neq ptr)\<close>
      subgoal for k
        apply (subgoal_tac "k < unat j")
         apply (subgoal_tac "copy_loop src_seg tgt_pre (unat addr) (unat (j + 1))
                  ! (unat tgt_pos + k) =
                copy_loop src_seg tgt_pre (unat addr) (unat j)
                  ! (unat tgt_pos + k)")
          apply simp
         apply (subgoal_tac "unat (j + 1) = Suc (unat j)")
          apply (subgoal_tac "unat tgt_pos = length tgt_pre")
           apply (simp only:)
           apply (rule copy_loop_nth_stable)
           apply assumption
          using tgt_pre_def apply simp
         using no_overflow_tgt apply unat_arith
        apply (cases "k = unat j")
         apply (simp add: word_unat.Rep_inverse)
        apply (subgoal_tac "unat (j + 1 :: 32 word) = unat j + 1")
         apply linarith
        using no_overflow_tgt by unat_arith
      \<comment> \<open>10. prefix preservation (eq ptr - impossible)\<close>
      subgoal for i
        apply (subgoal_tac "out +\<^sub>p int (unat tgt_pos + unat j) = out +\<^sub>p uint (tgt_pos + j)")
         using out_inj[rule_format, of i "unat tgt_pos + unat j"]
         apply (simp add: word_less_nat_alt)
        apply (subgoal_tac "unat (tgt_pos + j) = unat tgt_pos + unat j")
         apply (simp only: ptr_add_def uint_nat of_int_of_nat_eq)
        apply (rule iffD1[OF unat_add_lem])
        using no_overflow_tgt by (auto simp: word_less_nat_alt)
      \<comment> \<open>11. prefix preservation (neq ptr)\<close>
      subgoal by simp
      \<comment> \<open>12. termination\<close>
      subgoal
        apply (subgoal_tac "unat (j + 1 :: 32 word) = unat j + 1")
         apply (subgoal_tac "unat j < unat sz")
          apply linarith
         apply (simp only: word_less_nat_alt)
        using no_overflow_tgt by unat_arith
      done
    done
  done

(* ---------- Phase 2: Prefix refinement (no-source, no-app-header) ---------- *)

(*
  Prefix refinement lemma: the C decoder's execution from start to the main
  while-loop entry corresponds to parse_header + parse_window from the spec.

  Simplest success-path scenario:
    - Magic OK, hdr_indicator OK, no app header (bit 2 = 0)
    - code_tbl_built (skip build_code_table call)
    - win_ind: no source (bit 0 = 0), no target (bit 1 = 0), no adler32 (bit 2 = 0)
    - All varints (dlen, tgt_len, di=0, data_len, inst_len, addr_len) parse successfully
    - Section sizes consistent

  Postcondition: the state after prefix execution has:
    - data_cursor, inst_cursor, addr_cursor pointing to the three sections
    - tgt_pos = 0, near_ptr = 0
    - cache initialized to zero (near_arr, same_arr all zero)
    - Cursors match parse_window output
*)

(*
  Helper: varint_decode always returns a value < 2^32.
  (Used to discharge the nv_fits precondition of read_varint'_chain.)
*)
lemma varint_decode_fits:
  "varint_decode bs = Some (nv, rest) \<Longrightarrow> nv < 2 ^ 32"
  by (rule varint_decode_value_bound)

(*
  Helper: after a varint decode from drop k bs, the rest length < 2^32
  if the total buffer length < 2^32.
*)
lemma varint_rest_lt_2p32:
  assumes "varint_decode (drop k bs) = Some (nv, rest)"
      and "length bs < 2 ^ 32"
  shows "length rest < 2 ^ 32"
proof -
  have "length rest \<le> length (drop k bs)"
    by (rule varint_decode_length[OF assms(1)])
  also have "\<dots> \<le> length bs" by simp
  finally show ?thesis using assms(2) by linarith
qed

(*
  Helper: pop_byte on a non-empty drop gives the nth element.
*)
lemma pop_byte_drop:
  assumes "k < length bs"
  shows "pop_byte (drop k bs) = Some (bs ! k, drop (Suc k) bs)"
proof -
  have "drop k bs = bs ! k # drop (Suc k) bs"
    using assms by (simp add: Cons_nth_drop_Suc)
  thus ?thesis by (simp add: pop_byte_def)
qed

(*
  The prefix refinement for the no-source, no-app-header, code-table-built
  success path. Shows that after the C prefix, the cursor variables point
  to the correct sections matching parse_window.

  This lemma establishes the connection between the C state entering the
  main while-loop and the pure spec's parse_header + parse_window result.

  We state it in terms of varint_decode results on the patch bytes, since
  those are exactly what read_varint'_chain needs.
*)
lemma prefix_refine_no_source:
  assumes bs_def: "bs = heap_bytes s patch (unat patch_len)"
      and len_ge5: "5 \<le> unat patch_len"
      \<comment> \<open>Header: magic OK, hdr indicator OK, no app header\<close>
      and magic0: "bs ! 0 = 0xD6"
      and magic1: "bs ! 1 = 0xC3"
      and magic2: "bs ! 2 = 0xC4"
      and magic3: "bs ! 3 = 0x00"
      and hdr_ok: "bs ! 4 AND 0x03 = 0"
      and no_app: "bs ! 4 AND 0x04 = 0"
      \<comment> \<open>Window indicator: no source, no target, no adler32\<close>
      and win_ind_parse: "pop_byte (drop 5 bs) = Some (win_ind, wbs1)"
      and no_source: "win_ind AND 0x01 = 0"
      and no_target: "win_ind AND 0x02 = 0"
      and win_mask_ok: "win_ind AND 0xFA = 0"
      and no_adler: "win_ind AND 0x04 = 0"
      \<comment> \<open>Varint parses for window metadata\<close>
      and dlen_ok: "varint_decode wbs1 = Some (dlen, wbs2)"
      and tgt_ok: "varint_decode wbs2 = Some (tgt_len, wbs3)"
      and di_pop: "pop_byte wbs3 = Some (di_byte, wbs4)"
      and di_zero: "di_byte = 0"
      and data_ok: "varint_decode wbs4 = Some (data_len, wbs5)"
      and inst_ok: "varint_decode wbs5 = Some (inst_len, wbs6)"
      and addr_ok: "varint_decode wbs6 = Some (addr_len, wbs7)"
      \<comment> \<open>Section sizes fit\<close>
      and sizes_ok: "data_len + inst_len + addr_len \<le> length wbs7"
      and dlen_exact: "dlen = (length wbs2 - length wbs7) + data_len + inst_len + addr_len"
  shows "parse_header bs = Inl (drop 5 bs)
       \<and> parse_window (drop 5 bs) = Inl (\<lparr>
           pw_src_seg_len = 0,
           pw_src_seg_off = 0,
           pw_tgt_len = tgt_len,
           pw_data = take data_len wbs7,
           pw_inst = take inst_len (drop data_len wbs7),
           pw_addr = take addr_len (drop (data_len + inst_len) wbs7)
         \<rparr>, drop (data_len + inst_len + addr_len) wbs7)"
proof (intro conjI)
  show "parse_header bs = Inl (drop 5 bs)"
    by (rule parse_header_no_app[OF bs_def len_ge5 magic0 magic1 magic2 magic3 hdr_ok no_app])
next
  show "parse_window (drop 5 bs) = Inl (\<lparr>
           pw_src_seg_len = 0,
           pw_src_seg_off = 0,
           pw_tgt_len = tgt_len,
           pw_data = take data_len wbs7,
           pw_inst = take inst_len (drop data_len wbs7),
           pw_addr = take addr_len (drop (data_len + inst_len) wbs7)
         \<rparr>, drop (data_len + inst_len + addr_len) wbs7)"
    by (rule parse_window_no_source[OF win_ind_parse no_target win_mask_ok no_source
            no_adler dlen_ok tgt_ok di_pop di_zero data_ok inst_ok addr_ok sizes_ok
            dlen_exact])
qed

(*
  Helper: when pop_byte (drop 5 bs) = Some (w, rest), we have length bs >= 6
  and rest = drop 6 bs.
*)
lemma pop_byte_drop5:
  assumes "pop_byte (drop 5 bs) = Some (w, rest)"
      and "5 \<le> length bs"
  shows "length bs \<ge> 6 \<and> rest = drop 6 bs \<and> w = bs ! 5"
proof -
  have len5: "5 < length bs"
  proof (rule ccontr)
    assume "\<not> 5 < length bs"
    hence "length bs = 5" using assms(2) by simp
    hence "drop 5 bs = []" by simp
    with assms(1) show False by (simp add: pop_byte_def)
  qed
  hence eq: "drop 5 bs = bs ! 5 # drop 6 bs"
    using Cons_nth_drop_Suc[of 5 bs] by simp
  from assms(1) eq have "w = bs ! 5 \<and> rest = drop 6 bs"
    by (simp add: pop_byte_def)
  with len5 show ?thesis by linarith
qed

(*
  Init loops preserve heap_bytes of patch buffer.
  Stronger version that preserves the full buf_valid + heap_bytes combo.
*)
lemma near_init_preserves_patch_heap:
  "(whileLoop (\<lambda>idx st. unat idx < 4)
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word)
          \<and> heap_bytes t buf n = heap_bytes s0 buf n
          \<and> buf_valid t buf n = buf_valid s0 buf n
	          \<and> heap_w32 t p = heap_w32 s0 p
	          \<and> code_tbl_built_'' t = code_tbl_built_'' s0
	          \<and> code_tbl_'' t = code_tbl_'' s0
	          \<and> heap_typing t = heap_typing s0 \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 4 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 4
              \<and> heap_bytes st buf n = heap_bytes s0 buf n
              \<and> buf_valid st buf n = buf_valid s0 buf n
	              \<and> heap_w32 st p = heap_w32 s0 p
	              \<and> code_tbl_built_'' st = code_tbl_built_'' s0
	              \<and> code_tbl_'' st = code_tbl_'' s0
	              \<and> heap_typing st = heap_typing s0"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (clarsimp simp: word_less_nat_alt)
    apply (cases "unat idx")
     apply (auto simp: unat_word_ariths(1) word_less_nat_alt)
    done
  done

lemma same_init_preserves_patch_heap:
  "(whileLoop (\<lambda>idx st. unat idx < 768)
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (768 :: 32 word)
          \<and> heap_bytes t buf n = heap_bytes s0 buf n
          \<and> buf_valid t buf n = buf_valid s0 buf n
	          \<and> heap_w32 t p = heap_w32 s0 p
	          \<and> code_tbl_built_'' t = code_tbl_built_'' s0
	          \<and> code_tbl_'' t = code_tbl_'' s0
	          \<and> heap_typing t = heap_typing s0 \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 768 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 768
              \<and> heap_bytes st buf n = heap_bytes s0 buf n
              \<and> buf_valid st buf n = buf_valid s0 buf n
	              \<and> heap_w32 st p = heap_w32 s0 p
	              \<and> code_tbl_built_'' st = code_tbl_built_'' s0
	              \<and> code_tbl_'' st = code_tbl_'' s0
	              \<and> heap_typing st = heap_typing s0"])
  subgoal by simp
  subgoal by simp
  subgoal for idx st
    apply (clarsimp simp: word_less_nat_alt)
    apply (subst word_unat_eq_iff)
    apply simp
    done
  subgoal for idx st
    apply runs_to_vcg
    apply (clarsimp simp: word_less_nat_alt)
    apply (cases "unat idx")
     apply (auto simp: unat_word_ariths(1) word_less_nat_alt)
    done
  done

(*
  State transfer for read_varint'_chain: if the new state t has the same
  buf_valid and heap_bytes as s, then read_varint'_chain applies to t.
*)
lemma read_varint'_chain_transfer:
  assumes buf_ok: "buf_valid s buf (unat len)"
      and pos_ok: "pos \<le> len"
      and decode_ok: "varint_decode (drop (unat pos) (heap_bytes s buf (unat len)))
                     = Some (nv, rest)"
      and nv_fits: "nv < 2 ^ 32"
      and buf_eq: "buf_valid t buf (unat len)"
      and heap_eq: "heap_bytes t buf (unat len) = heap_bytes s buf (unat len)"
  shows "read_varint' buf len pos \<bullet> t
           \<lbrace> \<lambda>r t'. t' = t \<and>
                  r = Result (pr_t_C (len - of_nat (length rest))
                                     (of_nat nv) VCD_OK) \<and>
                  pos \<le> len - of_nat (length rest) \<and>
                  len - of_nat (length rest) \<le> len \<rbrace>"
proof -
  have decode_t: "varint_decode (drop (unat pos) (heap_bytes t buf (unat len)))
                  = Some (nv, rest)"
    using decode_ok heap_eq by simp
  show ?thesis by (rule read_varint'_chain[OF buf_eq pos_ok decode_t nv_fits])
qed

(*
  Varint chain helper: if varint_decode on drop k bs = Some (v, rest),
  and rest = drop (length bs - length rest) bs, then
  read_varint' at C position (patch_len - of_nat (length (drop k bs)))
  gives Result with pos = patch_len - of_nat (length rest).

  We use read_varint'_chain for each varint read. The key insight is:
  varint_decode (drop (unat pos) (heap_bytes s patch (unat patch_len))) = Some ...
  when pos = patch_len - of_nat (length suffix) where suffix starts at
  the current parse point.

  Position relation: drop k bs is a suffix of bs. If varint_decode
  (drop k bs) returns rest, the C position after the read is
  patch_len - of_nat (length rest). The next varint decode starts from
  the same position since drop (unat pos) bs = rest.
*)

(*
  Helper: varint_decode on drop succeeds implies the position is in range.
*)
lemma varint_decode_pos_le:
  assumes "varint_decode (drop k bs) = Some (v, rest)"
      and "k \<le> length bs"
  shows "length rest \<le> length bs"
proof -
  have "length rest \<le> length (drop k bs)"
    by (rule varint_decode_length[OF assms(1)])
  thus ?thesis using assms(2) by simp
qed

(*
  Helper: position word from varint rest length.
  If length rest \<le> unat patch_len and length rest < 2^32,
  then unat (patch_len - of_nat (length rest)) = unat patch_len - length rest,
  and the position is in [0, patch_len].
*)
lemma varint_pos_unat:
  fixes patch_len :: "32 word"
  assumes "length rest \<le> unat patch_len"
      and "length rest < 2 ^ 32"
  shows "unat (patch_len - of_nat (length rest) :: 32 word) = unat patch_len - length rest"
proof -
  have unat_rest: "unat (of_nat (length rest) :: 32 word) = length rest"
    using assms(2) by (simp add: unat_of_nat_eq)
  have le: "(of_nat (length rest) :: 32 word) \<le> patch_len"
    using assms(1) unat_rest by (simp add: word_le_nat_alt)
  show ?thesis using le unat_rest by (simp add: unat_sub)
qed

(*
  Helper: chaining varint decodes. If varint_decode on drop (unat pos) bs
  succeeds, and then varint_decode on the resulting rest also succeeds,
  we can express the second decode as varint_decode (drop (unat pos') bs)
  where pos' = patch_len - of_nat (length rest1).
*)
lemma varint_chain_drop:
  fixes patch_len :: "32 word"
  assumes first: "varint_decode (drop (unat pos) (heap_bytes s patch (unat patch_len)))
                  = Some (v1, rest1)"
      and second: "varint_decode rest1 = Some (v2, rest2)"
      and rest1_le: "length rest1 \<le> unat patch_len"
      and rest1_lt: "length rest1 < 2 ^ 32"
  shows "varint_decode (drop (unat (patch_len - of_nat (length rest1)))
                             (heap_bytes s patch (unat patch_len)))
         = Some (v2, rest2)"
proof -
  have unat_pos': "unat (patch_len - of_nat (length rest1) :: 32 word)
                   = unat patch_len - length rest1"
    by (rule varint_pos_unat[OF rest1_le rest1_lt])
  have drop_eq: "drop (unat patch_len - length rest1)
                      (heap_bytes s patch (unat patch_len)) = rest1"
    using varint_decode_drop_rest[OF first] rest1_le by simp
  show ?thesis using second drop_eq unat_pos' by simp
qed

(* ---------- Phase 3: Main decode loop invariant ---------- *)

(*
  The main decode loop invariant relates the C state (cursors, heap, cache arrays)
  to the pure spec's dec_state after some number of iterations.

  Parameters:
    s0      — initial state (before the loop; patch/src heap reference)
    patch, patch_n — patch buffer base and size
    src, src_n     — source buffer base and size
    out            — output buffer base
    src_seg_off, src_seg_len — source segment within src
    tgt_len        — expected target length (nat, from the varint)
    data_end, inst_end, addr_end — section end cursors (fixed)
    src_seg — precomputed source segment bytes (from src)

  Loop variables (5-tuple carried by the whileLoop):
    data_cursor, inst_cursor, addr_cursor — current read positions
    tgt_pos    — bytes written to output so far
    near_ptr   — cache rotation index

  The invariant says: there exists an abstract dec_state `dst` such that
  the remaining bytes in the patch (between cursor and end) equal the
  remaining abstract fields, the output built so far equals ds_tgt, and
  the cache arrays correspond to ds_cache.

  Because patch/src heaps are unchanged (writes only go to out), we can
  express the remaining byte slices via drop/take on the original heap_bytes.
*)
definition decode_loop_inv ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> nat \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   lifted_globals \<Rightarrow> bool" where
  "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
     data_end inst_end addr_end src_seg
     data_cursor inst_cursor addr_cursor tgt_pos np t =
   (\<exists>dst :: dec_state. \<exists>c :: cache.
      ds_inst_rem dst =
        drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n)) \<and>
      ds_data_rem dst =
        drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n)) \<and>
      ds_addr_rem dst =
        drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n)) \<and>
      ds_tgt dst = heap_bytes t out (unat tgt_pos) \<and>
      ds_cache dst = c \<and>
      cache_abs t c np \<and>
      cache_wf c \<and>
      \<comment> \<open>Heap preservation: patch and src unchanged from initial state\<close>
      (\<forall>i < patch_n. heap_w8 t (patch +\<^sub>p int i) = heap_w8 s0 (patch +\<^sub>p int i)) \<and>
      (\<forall>i < src_n. heap_w8 t (src +\<^sub>p int i) = heap_w8 s0 (src +\<^sub>p int i)) \<and>
      \<comment> \<open>Buffer validity preserved\<close>
      buf_valid t patch patch_n \<and>
      buf_valid t src src_n \<and>
      buf_valid t out tgt_len \<and>
      \<comment> \<open>Cursor bounds\<close>
      data_cursor \<le> data_end \<and>
      inst_cursor \<le> inst_end \<and>
      addr_cursor \<le> addr_end \<and>
      unat tgt_pos \<le> tgt_len \<and>
      \<comment> \<open>Section ends within patch buffer\<close>
      unat data_end \<le> patch_n \<and>
      unat inst_end \<le> patch_n \<and>
      unat addr_end \<le> patch_n \<and>
      \<comment> \<open>Code table still valid\<close>
      code_tbl_matches t \<and>
      \<comment> \<open>heap_typing unchanged (needed for ptr_valid preservation)\<close>
      heap_typing t = heap_typing s0 \<and>
      \<comment> \<open>Output pointer disjoint from patch and src\<close>
      (\<forall>i < tgt_len. \<forall>j < patch_n. out +\<^sub>p int i \<noteq> patch +\<^sub>p int j) \<and>
      (\<forall>i < tgt_len. \<forall>j < src_n. out +\<^sub>p int i \<noteq> src +\<^sub>p int j) \<and>
      \<comment> \<open>Output pointer injectivity\<close>
      (\<forall>i < tgt_len. \<forall>j < tgt_len. i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j) \<and>
      \<comment> \<open>No arithmetic overflow\<close>
      tgt_len < 2 ^ 32 \<and>
      unat src_seg_off + unat src_seg_len \<le> src_n \<and>
      unat src_seg_off + unat src_seg_len < 2 ^ 32 \<and>
      \<comment> \<open>Source segment definition\<close>
      src_seg = heap_bytes s0 (src +\<^sub>p uint src_seg_off) (unat src_seg_len))"

lemma decode_loop_invD:
  assumes "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
             data_end inst_end addr_end src_seg
             data_cursor inst_cursor addr_cursor tgt_pos np t"
  shows "\<forall>i < patch_n. heap_w8 t (patch +\<^sub>p int i) = heap_w8 s0 (patch +\<^sub>p int i)"
    and "\<forall>i < src_n. heap_w8 t (src +\<^sub>p int i) = heap_w8 s0 (src +\<^sub>p int i)"
    and "buf_valid t patch patch_n"
    and "buf_valid t src src_n"
    and "buf_valid t out tgt_len"
    and "data_cursor \<le> data_end"
    and "inst_cursor \<le> inst_end"
    and "addr_cursor \<le> addr_end"
    and "unat tgt_pos \<le> tgt_len"
    and "unat data_end \<le> patch_n"
    and "unat inst_end \<le> patch_n"
    and "unat addr_end \<le> patch_n"
    and "code_tbl_matches t"
    and "heap_typing t = heap_typing s0"
    and "\<forall>i < tgt_len. \<forall>j < patch_n. out +\<^sub>p int i \<noteq> patch +\<^sub>p int j"
    and "\<forall>i < tgt_len. \<forall>j < src_n. out +\<^sub>p int i \<noteq> src +\<^sub>p int j"
    and "\<forall>i < tgt_len. \<forall>j < tgt_len. i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j"
    and "tgt_len < 2 ^ 32"
    and "unat src_seg_off + unat src_seg_len \<le> src_n"
    and "unat src_seg_off + unat src_seg_len < 2 ^ 32"
    and "src_seg = heap_bytes s0 (src +\<^sub>p uint src_seg_off) (unat src_seg_len)"
  using assms by (auto simp: decode_loop_inv_def)


(*
  Strengthened outer-loop invariant for vcdiff_outer_loop_correct.

  The existing `decode_loop_inv` is sufficient for the instruction-level
  body-preservation proofs (add/run/copy lemmas), but its `dst` is
  existentially quantified: at exit we can't connect the witness to
  the pure spec's `decode_loop` trace.

  `decode_loop_inv_plus` adds a progress conjunct:
    ∃dst0 k. decode_loop k src_seg src_seg_len tgt_len dst0 = Inl dst ∧
             dst is the same witness decode_loop_inv has.

  At exit (inst_cursor = inst_end ⇒ ds_inst_rem dst = [] ⇒
  decode_loop terminates at this dst ⇒ length (ds_tgt dst) = tgt_len
  ⇒ heap_bytes t out (unat tgt_pos) = ds_tgt dst = target bytes),
  we can conclude the output-match claim.

  The progress parameter `dst0` represents the initial state at the
  start of the outer while-loop (after all prefix reads), and is fixed
  by the caller before invoking the invariant.
*)
definition decode_loop_inv_core ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> nat \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   dec_state \<Rightarrow> cache \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "decode_loop_inv_core s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
     data_end inst_end addr_end src_seg
     data_cursor inst_cursor addr_cursor tgt_pos np dst c t =
   (ds_inst_rem dst =
      drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n)) \<and>
    ds_data_rem dst =
      drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n)) \<and>
    ds_addr_rem dst =
      drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n)) \<and>
    ds_tgt dst = heap_bytes t out (unat tgt_pos) \<and>
    ds_cache dst = c \<and>
    cache_abs t c np \<and>
    cache_wf c \<and>
    (\<forall>i < patch_n. heap_w8 t (patch +\<^sub>p int i) = heap_w8 s0 (patch +\<^sub>p int i)) \<and>
    (\<forall>i < src_n. heap_w8 t (src +\<^sub>p int i) = heap_w8 s0 (src +\<^sub>p int i)) \<and>
    buf_valid t patch patch_n \<and>
    buf_valid t src src_n \<and>
    buf_valid t out tgt_len \<and>
    data_cursor \<le> data_end \<and>
    inst_cursor \<le> inst_end \<and>
    addr_cursor \<le> addr_end \<and>
    unat tgt_pos \<le> tgt_len \<and>
    unat data_end \<le> patch_n \<and>
    unat inst_end \<le> patch_n \<and>
    unat addr_end \<le> patch_n \<and>
    code_tbl_matches t \<and>
    heap_typing t = heap_typing s0 \<and>
    (\<forall>i < tgt_len. \<forall>j < patch_n. out +\<^sub>p int i \<noteq> patch +\<^sub>p int j) \<and>
    (\<forall>i < tgt_len. \<forall>j < src_n. out +\<^sub>p int i \<noteq> src +\<^sub>p int j) \<and>
    (\<forall>i < tgt_len. \<forall>j < tgt_len. i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j) \<and>
    tgt_len < 2 ^ 32 \<and>
    unat src_seg_off + unat src_seg_len \<le> src_n \<and>
    unat src_seg_off + unat src_seg_len < 2 ^ 32 \<and>
    src_seg = heap_bytes s0 (src +\<^sub>p uint src_seg_off) (unat src_seg_len))"

(*
  Equivalence of decode_loop_inv and its core-form with existentials.
*)
lemma decode_loop_inv_eq_core:
  "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
     data_end inst_end addr_end src_seg
     data_cursor inst_cursor addr_cursor tgt_pos np t
   \<longleftrightarrow>
   (\<exists>dst c. decode_loop_inv_core s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
            data_end inst_end addr_end src_seg
            data_cursor inst_cursor addr_cursor tgt_pos np dst c t)"
  unfolding decode_loop_inv_def decode_loop_inv_core_def by blast

(*
  Strengthened invariant.  The progress conjunct uses the "future fuel"
  formulation: from the current abstract state dst, decoding the remaining
  instructions terminates with the final target bytes.  `tgt` is the
  final output bytes, fixed by the caller (the pure spec's output for
  this input).

  This formulation holds at entry (with dst = dst0 and fuel =
  length (ds_inst_rem dst0)) and is preserved by each step (fuel
  decreases by 1 as dst advances by one decode_one).
*)
definition decode_loop_inv_plus ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow>
   8 word ptr \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> nat \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   byte list \<Rightarrow>
   byte list \<Rightarrow>
   32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   lifted_globals \<Rightarrow> bool" where
  "decode_loop_inv_plus s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
     data_end inst_end addr_end src_seg tgt
     data_cursor inst_cursor addr_cursor tgt_pos np t =
   (\<exists>dst c dst_final k.
      decode_loop_inv_core s0 patch patch_n src src_n out
                            src_seg_off src_seg_len tgt_len
                            data_end inst_end addr_end src_seg
                            data_cursor inst_cursor addr_cursor tgt_pos np
                            dst c t \<and>
      decode_loop k src_seg (unat src_seg_len) tgt_len dst
        = Inl dst_final \<and>
      length (ds_tgt dst_final) = tgt_len \<and>
      ds_tgt dst_final = tgt \<and>
      ds_data_rem dst_final = [] \<and>
      ds_addr_rem dst_final = [])"

(*
  At loop entry, invariant holds with dst = dst0 (zero iterations).
  dst0 is the initial abstract state derived from the parsed window.
*)
lemma decode_loop_inv_plus_entry:
  assumes core0: "decode_loop_inv_core s0 patch patch_n src src_n out
                   src_seg_off src_seg_len tgt_len
                   data_end inst_end addr_end src_seg
                   data_cursor inst_cursor addr_cursor 0 0
                   dst0 cache_init t0"
      and apply_ok:
        "\<exists>dst_final. decode_loop (length (ds_inst_rem dst0)) src_seg (unat src_seg_len) tgt_len dst0
                      = Inl dst_final \<and>
                     length (ds_tgt dst_final) = tgt_len \<and>
                     ds_tgt dst_final = tgt \<and>
                     ds_data_rem dst_final = [] \<and>
                     ds_addr_rem dst_final = []"
  shows "decode_loop_inv_plus s0 patch patch_n src src_n out
           src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg tgt
           data_cursor inst_cursor addr_cursor 0 0 t0"
  using core0 apply_ok
  unfolding decode_loop_inv_plus_def
  by blast

(*
  At exit (inst_cursor = inst_end), the invariant implies the pure spec's
  decode_loop has terminated with the current witness, and the output
  bytes match ds_tgt of the final abstract state.
*)
lemma decode_loop_inv_plus_exit:
  assumes inv: "decode_loop_inv_plus s0 patch patch_n src src_n out
                  src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg tgt
                  data_cursor inst_end addr_cursor tgt_pos np t"
      and ie_le: "unat inst_end \<le> patch_n"
  shows "heap_bytes t out (unat tgt_pos) = tgt \<and>
         unat tgt_pos = tgt_len \<and>
         unat tgt_pos = length tgt \<and>
         data_cursor = data_end \<and>
         addr_cursor = addr_end"
proof -
  obtain dst c dst_final k where
    core: "decode_loop_inv_core s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len data_end inst_end addr_end src_seg data_cursor inst_end addr_cursor tgt_pos np dst c t"
    and decloop: "decode_loop k src_seg (unat src_seg_len) tgt_len dst = Inl dst_final"
    and len: "length (ds_tgt dst_final) = tgt_len"
    and tgt_eq: "ds_tgt dst_final = tgt"
    and data_empty: "ds_data_rem dst_final = []"
    and addr_empty: "ds_addr_rem dst_final = []"
    using inv unfolding decode_loop_inv_plus_def by blast
  have inst_rem_empty: "ds_inst_rem dst = []"
  proof -
    from core have "ds_inst_rem dst =
         drop (unat inst_end) (take (unat inst_end) (heap_bytes s0 patch patch_n))"
      unfolding decode_loop_inv_core_def by simp
    thus ?thesis by simp
  qed
  have "decode_loop k src_seg (unat src_seg_len) tgt_len dst = Inl dst"
    using inst_rem_empty by (cases k) auto
  with decloop have "dst = dst_final" by simp
  with tgt_eq have ds_tgt_eq: "ds_tgt dst = tgt" by simp
  from core have "ds_tgt dst = heap_bytes t out (unat tgt_pos)"
    unfolding decode_loop_inv_core_def by simp
  with ds_tgt_eq have hb_eq: "heap_bytes t out (unat tgt_pos) = tgt" by simp
  have len_hb: "length (heap_bytes t out (unat tgt_pos)) = unat tgt_pos" by simp
  from hb_eq len_hb have pos_tgt: "unat tgt_pos = length tgt" by simp
  from len \<open>dst = dst_final\<close> ds_tgt_eq have "unat tgt_pos = tgt_len"
    using pos_tgt by simp
  have dc_eq: "data_cursor = data_end"
  proof -
    from core have data_rem:
      "ds_data_rem dst =
        drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n))"
      and dc_le: "data_cursor \<le> data_end"
      and de_le: "unat data_end \<le> patch_n"
      unfolding decode_loop_inv_core_def by auto
    from data_empty \<open>dst = dst_final\<close> data_rem have
      "drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n)) = []"
      by simp
    hence "unat data_end \<le> unat data_cursor"
      using de_le by (simp add: drop_eq_Nil)
    moreover from dc_le have "unat data_cursor \<le> unat data_end"
      by (simp add: word_le_nat_alt)
    ultimately have "unat data_cursor = unat data_end" by simp
    thus ?thesis by (simp add: word_unat.Rep_inject)
  qed
  have ac_eq: "addr_cursor = addr_end"
  proof -
    from core have addr_rem:
      "ds_addr_rem dst =
        drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n))"
      and ac_le: "addr_cursor \<le> addr_end"
      and ae_le: "unat addr_end \<le> patch_n"
      unfolding decode_loop_inv_core_def by auto
    from addr_empty \<open>dst = dst_final\<close> addr_rem have
      "drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n)) = []"
      by simp
    hence "unat addr_end \<le> unat addr_cursor"
      using ae_le by (simp add: drop_eq_Nil)
    moreover from ac_le have "unat addr_cursor \<le> unat addr_end"
      by (simp add: word_le_nat_alt)
    ultimately have "unat addr_cursor = unat addr_end" by simp
    thus ?thesis by (simp add: word_unat.Rep_inject)
  qed
  with dc_eq pos_tgt hb_eq \<open>unat tgt_pos = tgt_len\<close> show ?thesis by simp
qed

(*
  Helper: under decode_loop_inv_plus, the core inv holds with witness
  equal to the current state's dst.
*)
lemma decode_loop_inv_plus_coreD:
  assumes "decode_loop_inv_plus s0 patch patch_n src src_n out
             src_seg_off src_seg_len tgt_len
             data_end inst_end addr_end src_seg tgt
             data_cursor inst_cursor addr_cursor tgt_pos np t"
  shows "\<exists>dst c dst_final k.
           decode_loop_inv_core s0 patch patch_n src src_n out
             src_seg_off src_seg_len tgt_len
             data_end inst_end addr_end src_seg
             data_cursor inst_cursor addr_cursor tgt_pos np dst c t \<and>
           decode_loop k src_seg (unat src_seg_len) tgt_len dst
             = Inl dst_final \<and>
           length (ds_tgt dst_final) = tgt_len \<and>
           ds_tgt dst_final = tgt \<and>
           ds_data_rem dst_final = [] \<and>
           ds_addr_rem dst_final = []"
  using assms unfolding decode_loop_inv_plus_def by blast

(*
  Body-preservation lemma: one outer-loop iteration advances the
  invariant by one decode_one step.

  The progress conjunct updates naturally: from the old dst, fuel
  N = length (ds_inst_rem dst) gives Inl dst_final; from the new dst'
  (= one decode_one step further), fuel N-k (for some k ≥ 1 consumed)
  still gives the same dst_final because decode_loop is deterministic.
*)
(*
  Derive apply_window success + decode_loop termination from decode_spec = Inl.
*)
lemma apply_window_from_decode_spec:
  assumes "decode_spec bs src = Inl tgt"
      and "parse_header bs = Inl rest"
      and "parse_window rest = Inl (win, tail)"
  shows "apply_window win src = Inl tgt"
  using assms unfolding decode_spec_def by auto

lemma decode_loop_from_apply_window:
  assumes aw: "apply_window win src = Inl tgt"
      and src_seg_def:
        "(if pw_src_seg_len win = 0 then []
          else take (pw_src_seg_len win) (drop (pw_src_seg_off win) src)) = src_seg"
  shows "\<exists>dst.
           decode_loop (length (pw_inst win)) src_seg
             (pw_src_seg_len win) (pw_tgt_len win)
             \<lparr> ds_data_rem = pw_data win,
               ds_inst_rem = pw_inst win,
               ds_addr_rem = pw_addr win,
               ds_cache = cache_init,
               ds_tgt = [] \<rparr> = Inl dst \<and>
           length (ds_tgt dst) = pw_tgt_len win \<and>
           ds_tgt dst = tgt \<and>
           ds_data_rem dst = [] \<and>
           ds_addr_rem dst = []"
  using aw src_seg_def
  unfolding apply_window_def Let_def
  by (auto split: sum.splits if_splits)

(*
  Simple consequence: from inv_plus, inst_cursor ≤ inst_end.
  Avoids having to unfold definitions inside larger proofs.
*)
lemma decode_loop_inv_plus_ic_le:
  assumes "decode_loop_inv_plus s0 patch patch_n src src_n out src_seg_off src_seg_len
             tgt_len data_end inst_end addr_end src_seg tgt
             data_cursor inst_cursor addr_cursor tgt_pos np t"
  shows "inst_cursor \<le> inst_end"
  using assms
  unfolding decode_loop_inv_plus_def decode_loop_inv_core_def
  by blast

(*
  Corollary: decode_loop_inv_plus implies unat inst_end \<le> patch_n.
  Used to avoid passing ie_le as a separate hypothesis to the abstract
  whileLoop lemma.
*)
lemma decode_loop_inv_plus_ie_le:
  assumes "decode_loop_inv_plus s0 patch patch_n src src_n out src_seg_off src_seg_len
             tgt_len data_end inst_end addr_end src_seg tgt
             data_cursor inst_cursor addr_cursor tgt_pos np t"
  shows "unat inst_end \<le> patch_n"
  using assms
  unfolding decode_loop_inv_plus_def decode_loop_inv_core_def
  by blast

(*
  Abstract outer-loop correctness: given a body B that preserves
  decode_loop_inv_plus per iteration with strictly decreasing inst_rem,
  the whileLoop terminates with inst_cursor = inst_end and the
  invariant's exit consequences.

  The concrete C outer-loop body instantiates this lemma by discharging
  the body-preservation precondition (which captures the per-iteration
  Hoare triple: one opcode read + inner which-loop dispatch advances
  the abstract state by one decode_one).
*)
lemma outer_whileLoop_correct_abstract:
  fixes B :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word \<times> 32 word
              \<Rightarrow> (int, 32 word \<times> 32 word \<times> 32 word \<times> 32 word \<times> 32 word,
                  lifted_globals) exn_monad"
  assumes inv_entry:
    "decode_loop_inv_plus s0 patch patch_n src src_n out
       src_seg_off src_seg_len tgt_len
       data_end inst_end addr_end src_seg tgt
       data_pos inst_pos addr_pos 0 0 t0"
  assumes body_preserves:
    "\<And>ac dc ic np tp t. ic < inst_end \<Longrightarrow>
      decode_loop_inv_plus s0 patch patch_n src src_n out
        src_seg_off src_seg_len tgt_len
        data_end inst_end addr_end src_seg tgt
        dc ic ac tp np t \<Longrightarrow>
      B (ac, dc, ic, np, tp) \<bullet> t
        \<lbrace> \<lambda>r t'. (\<forall>ac' dc' ic' np' tp'. r = Result (ac', dc', ic', np', tp') \<longrightarrow>
              decode_loop_inv_plus s0 patch patch_n src src_n out
                src_seg_off src_seg_len tgt_len
                data_end inst_end addr_end src_seg tgt
                dc' ic' ac' tp' np' t' \<and>
              ic < ic') \<and>
              (\<forall>e. r = Exn e \<longrightarrow> e \<noteq> 0) \<rbrace>"
  shows "(whileLoop (\<lambda>(ac, dc, ic, np, tp) s. ic < inst_end) B
                    (addr_pos, data_pos, inst_pos, 0, 0)) \<bullet> t0
         \<lbrace> \<lambda>r t. (\<forall>ac dc ic np tp. r = Result (ac, dc, ic, np, tp) \<longrightarrow>
               ic = inst_end \<and>
               dc = data_end \<and>
               ac = addr_end \<and>
               heap_bytes t out (unat tp) = tgt \<and>
               unat tp = tgt_len) \<and>
               (\<forall>e. r = Exn e \<longrightarrow> e \<noteq> 0) \<rbrace>"
proof -
  have ie_le: "unat inst_end \<le> patch_n"
    using inv_entry by (rule decode_loop_inv_plus_ie_le)
  let ?I = "\<lambda>r t.
        (\<forall>ac dc ic np tp. r = Result (ac, dc, ic, np, tp) \<longrightarrow>
            decode_loop_inv_plus s0 patch patch_n src src_n out
              src_seg_off src_seg_len tgt_len
              data_end inst_end addr_end src_seg tgt
              dc ic ac tp np t) \<and>
        (\<forall>e. r = Exn e \<longrightarrow> e \<noteq> 0)"
  show ?thesis
    apply (rule runs_to_whileLoop_exn'
      [where I = ?I
         and R = "measure (\<lambda>((ac, dc, ic, np, tp), _). unat inst_end - unat ic)"])
    \<comment> \<open>Body preserves I.  I = (Result conj) ∧ (Exn conj).\<close>
    subgoal for a t
      apply clarsimp
      apply (rule runs_to_weaken[OF body_preserves])
        apply assumption
       apply blast
      apply (elim conjE)
      apply (intro conjI allI impI)
        \<comment> \<open>I r t' — Result conj.\<close>
        apply blast
       \<comment> \<open>I r t' — Exn conj.\<close>
       apply blast
      \<comment> \<open>Measure decrease.\<close>
      apply clarsimp
      apply (drule decode_loop_inv_plus_ic_le)
      apply (simp add: word_less_nat_alt word_le_nat_alt)
      done
    \<comment> \<open>Exit (Result, guard false) ⇒ postcondition.\<close>
    subgoal for a t
      apply (clarsimp simp: split_def)
      apply (frule decode_loop_inv_plus_ic_le)
      apply (subgoal_tac "ic = inst_end")
       prefer 2 apply (simp add: word_le_not_less)
      apply clarsimp
      apply (drule decode_loop_inv_plus_exit[OF _ ie_le])
      apply auto
      done
    \<comment> \<open>Exit (Exn e): carries e ≠ 0 from invariant.\<close>
    subgoal for a t by simp
    \<comment> \<open>wf.\<close>
    subgoal by simp
    \<comment> \<open>Initial invariant.\<close>
    subgoal using inv_entry by simp
    done
qed

lemma outer_whileLoop_correct_success_abstract:
  fixes B :: "32 word \<times> 32 word \<times> 32 word \<times> 32 word \<times> 32 word
              \<Rightarrow> (int, 32 word \<times> 32 word \<times> 32 word \<times> 32 word \<times> 32 word,
                  lifted_globals) exn_monad"
  assumes inv_entry:
    "decode_loop_inv_plus s0 patch patch_n src src_n out
       src_seg_off src_seg_len tgt_len
       data_end inst_end addr_end src_seg tgt
       data_pos inst_pos addr_pos 0 0 t0"
  assumes body_preserves:
    "\<And>ac dc ic np tp t. ic < inst_end \<Longrightarrow>
      decode_loop_inv_plus s0 patch patch_n src src_n out
        src_seg_off src_seg_len tgt_len
        data_end inst_end addr_end src_seg tgt
        dc ic ac tp np t \<Longrightarrow>
      B (ac, dc, ic, np, tp) \<bullet> t
        \<lbrace> \<lambda>r t'. (\<forall>ac' dc' ic' np' tp'. r = Result (ac', dc', ic', np', tp') \<longrightarrow>
              decode_loop_inv_plus s0 patch patch_n src src_n out
                src_seg_off src_seg_len tgt_len
                data_end inst_end addr_end src_seg tgt
                dc' ic' ac' tp' np' t' \<and>
              ic < ic') \<and>
              (\<forall>e. r = Exn e \<longrightarrow> False) \<rbrace>"
  shows "(whileLoop (\<lambda>(ac, dc, ic, np, tp) s. ic < inst_end) B
                    (addr_pos, data_pos, inst_pos, 0, 0)) \<bullet> t0
         \<lbrace> \<lambda>r t. (\<forall>ac dc ic np tp. r = Result (ac, dc, ic, np, tp) \<longrightarrow>
               ic = inst_end \<and>
               dc = data_end \<and>
               ac = addr_end \<and>
               heap_bytes t out (unat tp) = tgt \<and>
               unat tp = tgt_len) \<and>
               (\<forall>e. r = Exn e \<longrightarrow> False) \<rbrace>"
proof -
  have ie_le: "unat inst_end \<le> patch_n"
    using inv_entry by (rule decode_loop_inv_plus_ie_le)
  let ?I = "\<lambda>r t.
        (\<forall>ac dc ic np tp. r = Result (ac, dc, ic, np, tp) \<longrightarrow>
            decode_loop_inv_plus s0 patch patch_n src src_n out
              src_seg_off src_seg_len tgt_len
              data_end inst_end addr_end src_seg tgt
              dc ic ac tp np t) \<and>
        (\<forall>e. r = Exn e \<longrightarrow> False)"
  show ?thesis
    apply (rule runs_to_whileLoop_exn'
      [where I = ?I
         and R = "measure (\<lambda>((ac, dc, ic, np, tp), _). unat inst_end - unat ic)"])
    subgoal for a t
      apply clarsimp
      apply (rule runs_to_weaken[OF body_preserves])
        apply assumption
       apply blast
      apply (elim conjE)
      apply (intro conjI allI impI)
        apply blast
       apply blast
      apply clarsimp
      apply (drule decode_loop_inv_plus_ic_le)
      apply (simp add: word_less_nat_alt word_le_nat_alt)
      done
    subgoal for a t
      apply (clarsimp simp: split_def)
      apply (frule decode_loop_inv_plus_ic_le)
      apply (subgoal_tac "ic = inst_end")
       prefer 2 apply (simp add: word_le_not_less)
      apply clarsimp
      apply (frule decode_loop_inv_plus_coreD)
      apply (drule decode_loop_inv_plus_exit[OF _ ie_le])
      apply (auto simp: decode_loop_inv_core_def)
      done
    subgoal for a t by simp
    subgoal by simp
    subgoal using inv_entry by simp
    done
qed

(*
  Fuel monotonicity: if decode_loop k dst = Inl f, then for any
  k' ≥ k, decode_loop k' dst = Inl f.  Once the decoder reaches
  ds_inst_rem = [], extra fuel is ignored.
*)
lemma decode_loop_fuel_mono:
  "decode_loop k src_seg src_seg_len tgt_len dst = Inl f \<Longrightarrow>
   k \<le> k' \<Longrightarrow>
   decode_loop k' src_seg src_seg_len tgt_len dst = Inl f"
proof (induction k arbitrary: k' dst)
  case 0
  hence "ds_inst_rem dst = []" by (cases "ds_inst_rem dst = []") auto
  with 0 show ?case by (cases k') (auto)
next
  case (Suc k)
  show ?case
  proof (cases "ds_inst_rem dst = []")
    case True
    with Suc.prems(1) have "f = dst" by simp
    with True Suc.prems(2) show ?thesis by (cases k') auto
  next
    case False
    from Suc.prems(1) False obtain st' where
      do: "decode_one src_seg src_seg_len tgt_len dst = Inl st'" and
      rec: "decode_loop k src_seg src_seg_len tgt_len st' = Inl f"
      by (cases "decode_one src_seg src_seg_len tgt_len dst") auto
    from Suc.prems(2) obtain k'' where k'_eq: "k' = Suc k''" "k \<le> k''"
      by (cases k') auto
    from Suc.IH[OF rec \<open>k \<le> k''\<close>] have
      "decode_loop k'' src_seg src_seg_len tgt_len st' = Inl f" .
    with k'_eq do False show ?thesis by simp
  qed
qed

(*
  Step lemma: decode_loop from dst reduces to decode_loop from dst'
  when decode_one dst = Inl dst'.
*)
lemma decode_loop_step:
  assumes "ds_inst_rem dst \<noteq> []"
      and "decode_one src_seg src_seg_len tgt_len dst = Inl dst'"
  shows "decode_loop (Suc k) src_seg src_seg_len tgt_len dst =
         decode_loop k src_seg src_seg_len tgt_len dst'"
  using assms by simp

lemma decode_loop_inv_plus_advance:
  assumes inv: "decode_loop_inv_plus s0 patch patch_n src src_n out
                  src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg tgt
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
      and progressing: "inst_cursor < inst_end"
      \<comment> \<open>The body's transition: from old dst in state t, one decode_one
          step to new dst' in state t', with cursor advancement.\<close>
      and core_before:
        "decode_loop_inv_core s0 patch patch_n src src_n out
           src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           data_cursor inst_cursor addr_cursor tgt_pos np dst (ds_cache dst) t"
      and step: "decode_one src_seg (unat src_seg_len) tgt_len dst = Inl dst'"
      and core_after:
        "decode_loop_inv_core s0 patch patch_n src src_n out
           src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           data_cursor' inst_cursor' addr_cursor' tgt_pos' np' dst' (ds_cache dst') t'"
      and inst_decreasing:
        "length (ds_inst_rem dst') < length (ds_inst_rem dst)"
  shows "decode_loop_inv_plus s0 patch patch_n src src_n out
           src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg tgt
           data_cursor' inst_cursor' addr_cursor' tgt_pos' np' t'"
proof -
  obtain dst_prev c_prev dst_final k_prev where
    prev_core: "decode_loop_inv_core s0 patch patch_n src src_n out
                  src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np dst_prev c_prev t"
    and decloop: "decode_loop k_prev src_seg (unat src_seg_len) tgt_len dst_prev = Inl dst_final"
    and len: "length (ds_tgt dst_final) = tgt_len"
    and tgt_eq: "ds_tgt dst_final = tgt"
    and data_empty: "ds_data_rem dst_final = []"
    and addr_empty: "ds_addr_rem dst_final = []"
    using inv unfolding decode_loop_inv_plus_def by blast
  \<comment> \<open>Show dst_prev = dst (records fully determined by fields).\<close>
  have dst_eq: "dst_prev = dst"
  proof -
    from prev_core core_before have fields:
      "ds_inst_rem dst_prev = ds_inst_rem dst"
      "ds_data_rem dst_prev = ds_data_rem dst"
      "ds_addr_rem dst_prev = ds_addr_rem dst"
      "ds_tgt dst_prev = ds_tgt dst"
      unfolding decode_loop_inv_core_def by auto
    have cache_eq: "ds_cache dst_prev = ds_cache dst"
    proof -
      have prev_cache_eq: "ds_cache dst_prev = c_prev"
        using prev_core unfolding decode_loop_inv_core_def by simp
      have prev_abs: "cache_abs t c_prev np"
        using prev_core unfolding decode_loop_inv_core_def by simp
      have prev_wf: "cache_wf c_prev"
        using prev_core unfolding decode_loop_inv_core_def by simp
      have cur_abs: "cache_abs t (ds_cache dst) np"
        using core_before unfolding decode_loop_inv_core_def by simp
      have cur_wf: "cache_wf (ds_cache dst)"
        using core_before unfolding decode_loop_inv_core_def by simp
      from cache_abs_unique[OF prev_abs prev_wf cur_abs cur_wf]
      show ?thesis by (simp add: prev_cache_eq)
    qed
    show ?thesis
      apply (rule dec_state.equality)
      using fields cache_eq by auto
  qed
  \<comment> \<open>ds_inst_rem dst is non-empty (progress check).\<close>
  have inst_nonempty: "ds_inst_rem dst \<noteq> []"
  proof -
    from core_before have
      "ds_inst_rem dst = drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))"
      unfolding decode_loop_inv_core_def by simp
    moreover from core_before have "unat inst_end \<le> patch_n"
      unfolding decode_loop_inv_core_def by simp
    moreover from progressing have "unat inst_cursor < unat inst_end"
      by (simp add: word_less_nat_alt)
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>k_prev must be ≥ 1 (decode_loop 0 on non-empty inst_rem returns Inr).\<close>
  have k_prev_pos: "k_prev \<ge> 1"
  proof (rule ccontr)
    assume "\<not> k_prev \<ge> 1"
    hence "k_prev = 0" by simp
    with decloop inst_nonempty dst_eq show False by simp
  qed
  then obtain k' where k_eq: "k_prev = Suc k'" by (cases k_prev) auto
  \<comment> \<open>Step: decloop = decode_loop k' dst'.\<close>
  have rec: "decode_loop k' src_seg (unat src_seg_len) tgt_len dst' = Inl dst_final"
    using decloop[unfolded dst_eq k_eq] inst_nonempty step
    by (subst (asm) decode_loop_step[OF inst_nonempty step]) simp
  \<comment> \<open>The new invariant with fuel k'.\<close>
  show ?thesis
    unfolding decode_loop_inv_plus_def
    using core_after rec len tgt_eq data_empty addr_empty
    by blast
qed


(*
  Key structural lemma: the invariant at the loop entry (initial state).
  After the prefix sets up cursors, the invariant holds with:
    - inst_cursor = inst_pos (start of instruction section)
    - data_cursor = data_pos (start of data section)
    - addr_cursor = addr_pos (start of addr section)
    - tgt_pos = 0
    - near_ptr = 0
    - cache = cache_init
*)
lemma decode_loop_inv_init:
  assumes heap_eq: "\<forall>i < patch_n. heap_w8 t (patch +\<^sub>p int i) = heap_w8 s0 (patch +\<^sub>p int i)"
      and src_eq: "\<forall>i < src_n. heap_w8 t (src +\<^sub>p int i) = heap_w8 s0 (src +\<^sub>p int i)"
      and patch_valid: "buf_valid t patch patch_n"
      and src_valid: "buf_valid t src src_n"
      and out_valid: "buf_valid t out tgt_len"
      and cache_init_abs: "cache_abs t cache_init 0"
      and cursor_bounds: "data_cursor \<le> data_end" "inst_cursor \<le> inst_end"
                         "addr_cursor \<le> addr_end" "unat (0 :: 32 word) \<le> tgt_len"
      and end_bounds: "unat data_end \<le> patch_n" "unat inst_end \<le> patch_n"
                      "unat addr_end \<le> patch_n"
      and code_tbl_ok: "code_tbl_matches t"
      and typing_eq: "heap_typing t = heap_typing s0"
      and out_disj_patch: "\<forall>i < tgt_len. \<forall>j < patch_n. out +\<^sub>p int i \<noteq> patch +\<^sub>p int j"
      and out_disj_src: "\<forall>i < tgt_len. \<forall>j < src_n. out +\<^sub>p int i \<noteq> src +\<^sub>p int j"
      and out_inj: "\<forall>i < tgt_len. \<forall>j < tgt_len. i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j"
      and tgt_len_fits: "tgt_len < 2 ^ 32"
      and src_seg_bounds: "unat src_seg_off + unat src_seg_len \<le> src_n"
                          "unat src_seg_off + unat src_seg_len < 2 ^ 32"
      and src_seg_eq: "src_seg = heap_bytes s0 (src +\<^sub>p uint src_seg_off) (unat src_seg_len)"
  shows "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           data_cursor inst_cursor addr_cursor 0 0 t"
proof -
  let ?pb = "heap_bytes s0 patch patch_n"
  have wf: "cache_wf cache_init"
  proof (unfold cache_wf_def, intro conjI allI impI)
    show "length (near cache_init) = s_near"
      by (simp add: cache_init_def s_near_def)
    show "length (same cache_init) = same_buckets"
      by (simp add: cache_init_def same_buckets_def s_same_def)
    show "AddressCache.near_ptr cache_init < s_near"
      by (simp add: cache_init_def s_near_def)
    fix i :: nat assume "i < s_near"
    hence "i < length (near cache_init)" by (simp add: cache_init_def s_near_def)
    hence "near cache_init ! i \<in> set (near cache_init)" by (rule nth_mem)
    moreover have "set (near cache_init) = {0}" by (simp add: cache_init_def s_near_def)
    ultimately show "near cache_init ! i < 2 ^ 32" by simp
  next
    fix i :: nat assume "i < same_buckets"
    hence "i < length (same cache_init)"
      by (simp add: cache_init_def same_buckets_def s_same_def)
    hence "same cache_init ! i \<in> set (same cache_init)" by (rule nth_mem)
    moreover have "set (same cache_init) = {0}"
      by (simp add: cache_init_def same_buckets_def s_same_def set_replicate_conv_if)
    ultimately show "same cache_init ! i < 2 ^ 32" by simp
  qed
  have tgt0: "heap_bytes t out (unat (0 :: 32 word)) = []"
    by (simp add: heap_bytes_def)
  show ?thesis
    unfolding decode_loop_inv_def
    apply (rule exI[where x = "\<lparr> ds_data_rem =
         drop (unat data_cursor) (take (unat data_end) ?pb),
       ds_inst_rem =
         drop (unat inst_cursor) (take (unat inst_end) ?pb),
       ds_addr_rem =
         drop (unat addr_cursor) (take (unat addr_end) ?pb),
       ds_cache = cache_init,
       ds_tgt = [] \<rparr>"])
    apply (rule exI[where x = "cache_init"])
    using heap_eq src_eq patch_valid src_valid out_valid cache_init_abs
          cursor_bounds end_bounds code_tbl_ok typing_eq out_disj_patch out_disj_src
          out_inj tgt_len_fits src_seg_bounds src_seg_eq wf tgt0
    by simp
qed

(*
  Core-form variant: same hypotheses, but the conclusion gives the
  explicit dst0 witness needed by decode_loop_inv_plus_entry.
*)
lemma decode_loop_inv_init_core:
  assumes heap_eq: "\<forall>i < patch_n. heap_w8 t (patch +\<^sub>p int i) = heap_w8 s0 (patch +\<^sub>p int i)"
      and src_eq: "\<forall>i < src_n. heap_w8 t (src +\<^sub>p int i) = heap_w8 s0 (src +\<^sub>p int i)"
      and patch_valid: "buf_valid t patch patch_n"
      and src_valid: "buf_valid t src src_n"
      and out_valid: "buf_valid t out tgt_len"
      and cache_init_abs: "cache_abs t cache_init 0"
      and cursor_bounds: "data_cursor \<le> data_end" "inst_cursor \<le> inst_end"
                         "addr_cursor \<le> addr_end"
      and end_bounds: "unat data_end \<le> patch_n" "unat inst_end \<le> patch_n"
                      "unat addr_end \<le> patch_n"
      and code_tbl_ok: "code_tbl_matches t"
      and typing_eq: "heap_typing t = heap_typing s0"
      and out_disj_patch: "\<forall>i < tgt_len. \<forall>j < patch_n. out +\<^sub>p int i \<noteq> patch +\<^sub>p int j"
      and out_disj_src: "\<forall>i < tgt_len. \<forall>j < src_n. out +\<^sub>p int i \<noteq> src +\<^sub>p int j"
      and out_inj: "\<forall>i < tgt_len. \<forall>j < tgt_len. i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j"
      and tgt_len_fits: "tgt_len < 2 ^ 32"
      and src_seg_bounds: "unat src_seg_off + unat src_seg_len \<le> src_n"
                          "unat src_seg_off + unat src_seg_len < 2 ^ 32"
      and src_seg_eq: "src_seg = heap_bytes s0 (src +\<^sub>p uint src_seg_off) (unat src_seg_len)"
  shows "decode_loop_inv_core s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           data_cursor inst_cursor addr_cursor 0 0
           \<lparr> ds_data_rem = drop (unat data_cursor) (take (unat data_end)
                                   (heap_bytes s0 patch patch_n)),
             ds_inst_rem = drop (unat inst_cursor) (take (unat inst_end)
                                   (heap_bytes s0 patch patch_n)),
             ds_addr_rem = drop (unat addr_cursor) (take (unat addr_end)
                                   (heap_bytes s0 patch patch_n)),
             ds_cache = cache_init,
             ds_tgt = [] \<rparr>
           cache_init t"
proof -
  have wf: "cache_wf cache_init"
  proof (unfold cache_wf_def, intro conjI allI impI)
    show "length (near cache_init) = s_near"
      by (simp add: cache_init_def s_near_def)
    show "length (same cache_init) = same_buckets"
      by (simp add: cache_init_def same_buckets_def s_same_def)
    show "AddressCache.near_ptr cache_init < s_near"
      by (simp add: cache_init_def s_near_def)
    fix i :: nat assume "i < s_near"
    hence "i < length (near cache_init)" by (simp add: cache_init_def s_near_def)
    hence "near cache_init ! i \<in> set (near cache_init)" by (rule nth_mem)
    moreover have "set (near cache_init) = {0}" by (simp add: cache_init_def s_near_def)
    ultimately show "near cache_init ! i < 2 ^ 32" by simp
  next
    fix i :: nat assume "i < same_buckets"
    hence "i < length (same cache_init)"
      by (simp add: cache_init_def same_buckets_def s_same_def)
    hence "same cache_init ! i \<in> set (same cache_init)" by (rule nth_mem)
    moreover have "set (same cache_init) = {0}"
      by (simp add: cache_init_def same_buckets_def s_same_def set_replicate_conv_if)
    ultimately show "same cache_init ! i < 2 ^ 32" by simp
  qed
  have tgt0: "heap_bytes t out (unat (0 :: 32 word)) = []"
    by (simp add: heap_bytes_def)
  show ?thesis
    unfolding decode_loop_inv_core_def
    using heap_eq src_eq patch_valid src_valid out_valid cache_init_abs
          cursor_bounds end_bounds code_tbl_ok typing_eq out_disj_patch out_disj_src
          out_inj tgt_len_fits src_seg_bounds src_seg_eq wf tgt0
    by simp
qed

lemma decode_loop_inv_plus_entry_from_init:
  assumes patch_bytes: "heap_bytes t patch patch_n = heap_bytes s0 patch patch_n"
      and src_bytes: "heap_bytes t src src_n = heap_bytes s0 src src_n"
      and patch_valid: "buf_valid t patch patch_n"
      and src_valid: "buf_valid t src src_n"
      and out_valid: "buf_valid t out tgt_len"
      and cache_init_abs: "cache_abs t cache_init 0"
      and cursor_bounds: "data_cursor \<le> data_end" "inst_cursor \<le> inst_end"
                         "addr_cursor \<le> addr_end"
      and end_bounds: "unat data_end \<le> patch_n" "unat inst_end \<le> patch_n"
                      "unat addr_end \<le> patch_n"
      and code_tbl_ok: "code_tbl_matches t"
      and typing_eq: "heap_typing t = heap_typing s0"
      and out_disj_patch: "\<forall>i < tgt_len. \<forall>j < patch_n. out +\<^sub>p int i \<noteq> patch +\<^sub>p int j"
      and out_disj_src: "\<forall>i < tgt_len. \<forall>j < src_n. out +\<^sub>p int i \<noteq> src +\<^sub>p int j"
      and out_inj: "\<forall>i < tgt_len. \<forall>j < tgt_len. i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j"
      and tgt_len_fits: "tgt_len < 2 ^ 32"
      and src_seg_bounds: "unat src_seg_off + unat src_seg_len \<le> src_n"
                          "unat src_seg_off + unat src_seg_len < 2 ^ 32"
      and src_seg_eq: "src_seg = heap_bytes s0 (src +\<^sub>p uint src_seg_off) (unat src_seg_len)"
      and apply_ok:
        "\<exists>dst_final.
           decode_loop (length (drop (unat inst_cursor)
                                (take (unat inst_end) (heap_bytes s0 patch patch_n))))
             src_seg (unat src_seg_len) tgt_len
             \<lparr> ds_data_rem = drop (unat data_cursor)
                                (take (unat data_end) (heap_bytes s0 patch patch_n)),
               ds_inst_rem = drop (unat inst_cursor)
                                (take (unat inst_end) (heap_bytes s0 patch patch_n)),
               ds_addr_rem = drop (unat addr_cursor)
                                (take (unat addr_end) (heap_bytes s0 patch patch_n)),
               ds_cache = cache_init,
               ds_tgt = [] \<rparr> = Inl dst_final \<and>
             length (ds_tgt dst_final) = tgt_len \<and>
             ds_tgt dst_final = tgt \<and>
             ds_data_rem dst_final = [] \<and>
             ds_addr_rem dst_final = []"
  shows "decode_loop_inv_plus s0 patch patch_n src src_n out
           src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg tgt
           data_cursor inst_cursor addr_cursor 0 0 t"
proof -
  let ?dst0 =
    "\<lparr> ds_data_rem = drop (unat data_cursor)
                         (take (unat data_end) (heap_bytes s0 patch patch_n)),
       ds_inst_rem = drop (unat inst_cursor)
                         (take (unat inst_end) (heap_bytes s0 patch patch_n)),
       ds_addr_rem = drop (unat addr_cursor)
                         (take (unat addr_end) (heap_bytes s0 patch patch_n)),
       ds_cache = cache_init,
       ds_tgt = [] \<rparr>"
  have patch_eq:
    "\<forall>i < patch_n. heap_w8 t (patch +\<^sub>p int i) = heap_w8 s0 (patch +\<^sub>p int i)"
    using patch_bytes by (auto dest: heap_bytes_eq_heap_w8D)
  have src_eq:
    "\<forall>i < src_n. heap_w8 t (src +\<^sub>p int i) = heap_w8 s0 (src +\<^sub>p int i)"
    using src_bytes by (auto dest: heap_bytes_eq_heap_w8D)
  have core:
    "decode_loop_inv_core s0 patch patch_n src src_n out
       src_seg_off src_seg_len tgt_len
       data_end inst_end addr_end src_seg
       data_cursor inst_cursor addr_cursor 0 0
       ?dst0 cache_init t"
    by (rule decode_loop_inv_init_core[OF patch_eq src_eq patch_valid src_valid
          out_valid cache_init_abs cursor_bounds end_bounds code_tbl_ok typing_eq
          out_disj_patch out_disj_src out_inj tgt_len_fits src_seg_bounds src_seg_eq])
  have apply_ok':
    "\<exists>dst_final. decode_loop (length (ds_inst_rem ?dst0)) src_seg
        (unat src_seg_len) tgt_len ?dst0 = Inl dst_final \<and>
       length (ds_tgt dst_final) = tgt_len \<and>
       ds_tgt dst_final = tgt \<and>
       ds_data_rem dst_final = [] \<and>
       ds_addr_rem dst_final = []"
    using apply_ok by simp
  show ?thesis
    by (rule decode_loop_inv_plus_entry[OF core apply_ok'])
qed

(*
  Key lemma: reading a byte at inst_cursor in the C corresponds to pop_byte
  on ds_inst_rem in the invariant.
*)
lemma inv_pop_byte_cursor:
  assumes "unat cursor < unat end_pos"
      and "unat (end_pos :: 32 word) \<le> n"
  shows "drop (unat cursor) (take (unat end_pos) (heap_bytes s0 buf n))
         = heap_w8 s0 (buf +\<^sub>p int (unat cursor))
           # drop (Suc (unat cursor)) (take (unat end_pos) (heap_bytes s0 buf n))"
proof -
  let ?bs = "heap_bytes s0 buf n"
  let ?tbs = "take (unat end_pos) ?bs"
  have len: "length ?tbs = unat end_pos" using assms(2) by simp
  have idx_lt: "unat cursor < length ?tbs" using assms(1) len by simp
  have drop_cons: "?tbs ! (unat cursor) # drop (Suc (unat cursor)) ?tbs = drop (unat cursor) ?tbs"
    by (rule Cons_nth_drop_Suc[OF idx_lt])
  hence drop_eq: "drop (unat cursor) ?tbs = ?tbs ! (unat cursor) # drop (Suc (unat cursor)) ?tbs"
    by simp
  have nth_eq: "?tbs ! (unat cursor) = ?bs ! (unat cursor)"
    using assms(1,2) by simp
  have byte_eq: "?bs ! (unat cursor) = heap_w8 s0 (buf +\<^sub>p int (unat cursor))"
    using assms(1,2) by (simp add: heap_bytes_nth)
  show ?thesis using drop_eq nth_eq byte_eq by simp
qed

(*
  Relating cursor advancement to drop on the abstract byte list.
  When we advance inst_cursor by 1 (after reading a byte), the remaining
  instruction bytes become drop (Suc (unat inst_cursor)) (take ...).
*)
lemma cursor_advance_drop:
  fixes cursor :: "32 word" and end_pos :: "32 word"
  assumes "unat cursor < unat end_pos"
      and "unat end_pos \<le> n"
      and "unat cursor + 1 < 2 ^ 32"
  shows "drop (unat (cursor + 1)) (take (unat end_pos) (heap_bytes s0 buf n))
         = drop (Suc (unat cursor)) (take (unat end_pos) (heap_bytes s0 buf n))"
proof -
  have "unat (cursor + 1 :: 32 word) = Suc (unat cursor)"
    using assms(3) by (simp add: unat_word_ariths(1))
  thus ?thesis by simp
qed

(*
  The drop/take length: length of remaining bytes equals end - cursor.
*)
lemma remaining_bytes_length:
  assumes "unat cursor \<le> unat end_pos"
      and "unat end_pos \<le> n"
  shows "length (drop (unat cursor) (take (unat end_pos) (heap_bytes s0 buf n)))
         = unat end_pos - unat cursor"
  using assms by simp

(*
  Lemma connecting code_tbl_matches to default_entry lookup.
  Under code_tbl_matches, reading code_tbl[op] gives entry_of_row matching
  default_entry (unat op).
*)
lemma code_tbl_matches_lookup:
  assumes "code_tbl_matches s"
      and "unat (op :: 8 word) < 256"
  shows "entry_of_row (code_tbl_'' s .[unat op]) = default_entry (unat op)"
  using assms by (simp add: code_tbl_matches_def)

(*
  Connecting pop_byte on the spec side to the invariant's cursor read.
  When inst_cursor < inst_end, the byte at inst_cursor is the head of
  ds_inst_rem, and advancing the cursor by 1 drops it.
*)
lemma inv_inst_pop_byte:
  fixes inst_cursor :: "32 word" and inst_end :: "32 word"
  assumes ic_lt: "unat inst_cursor < unat inst_end"
      and end_bd: "unat inst_end \<le> patch_n"
  shows "pop_byte (drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n)))
         = Some (heap_w8 s0 (patch +\<^sub>p int (unat inst_cursor)),
                 drop (Suc (unat inst_cursor)) (take (unat inst_end) (heap_bytes s0 patch patch_n)))"
proof -
  have pop: "drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))
             = heap_w8 s0 (patch +\<^sub>p int (unat inst_cursor))
               # drop (Suc (unat inst_cursor)) (take (unat inst_end) (heap_bytes s0 patch patch_n))"
    using inv_pop_byte_cursor[OF ic_lt end_bd] by simp
  thus ?thesis by (simp add: pop_byte_def)
qed

(*
  ADD half-instruction correspondence: when exec_half succeeds for IADD,
  the spec advances ds_data_rem by sz and appends those bytes to ds_tgt.
  The C implementation uses the add_loop inner loop which does the same
  (proved in add_loop_correct).
*)

(*
  ADD half-instruction: invariant preservation.
  When exec_half for IADD succeeds, it advances data_cursor by sz and
  tgt_pos by sz. The spec drops sz from ds_data_rem and appends those
  bytes to ds_tgt. The C's add_loop_correct shows the heap matches.

  This lemma says: after the ADD inner loop finishes (per add_loop_correct),
  the invariant is restored with updated cursors.
*)
lemma decode_loop_inv_after_add:
  fixes sz :: "32 word"
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
      and sz_pos: "0 < unat sz"
      and sz_fits_data: "unat sz \<le> unat data_end - unat data_cursor"
      and sz_fits_tgt: "unat tgt_pos + unat sz \<le> tgt_len"
      and no_overflow_data: "unat data_cursor + unat sz < 2 ^ 32"
      and no_overflow_tgt: "unat tgt_pos + unat sz < 2 ^ 32"
      \<comment> \<open>After the add loop: heap state t' has the ADD bytes written\<close>
      and patch_preserved: "\<forall>j < patch_n. heap_w8 t' (patch +\<^sub>p int j) = heap_w8 s0 (patch +\<^sub>p int j)"
      and src_preserved: "\<forall>j < src_n. heap_w8 t' (src +\<^sub>p int j) = heap_w8 s0 (src +\<^sub>p int j)"
      and add_result: "\<forall>j < unat sz. heap_w8 t' (out +\<^sub>p uint (tgt_pos + of_nat j)) =
                         heap_w8 s0 (patch +\<^sub>p uint (data_cursor + of_nat j))"
      and out_prefix_preserved: "\<forall>i < unat tgt_pos. heap_w8 t' (out +\<^sub>p int i) = heap_w8 t (out +\<^sub>p int i)"
      and typing_preserved: "heap_typing t' = heap_typing t"
      and cache_preserved: "near_arr_'' t' = near_arr_'' t"
                           "same_arr_'' t' = same_arr_'' t"
      and code_tbl_preserved: "code_tbl_'' t' = code_tbl_'' t"
  shows "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           (data_cursor + sz) inst_cursor addr_cursor (tgt_pos + sz) np t'"
proof -
  note invD = decode_loop_invD[OF inv]
  \<comment> \<open>Extract the abstract state from the invariant\<close>
  obtain dst :: dec_state and c :: cache where
    dst_inst: "ds_inst_rem dst =
      drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))" and
    dst_data: "ds_data_rem dst =
      drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n))" and
    dst_addr: "ds_addr_rem dst =
      drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n))" and
    dst_tgt: "ds_tgt dst = heap_bytes t out (unat tgt_pos)" and
    dst_cache: "ds_cache dst = c" and
    cache_ok: "cache_abs t c np" and
    cwf: "cache_wf c"
    using inv unfolding decode_loop_inv_def by blast
  \<comment> \<open>Cursor arithmetic\<close>
  have unat_dc_sz: "unat (data_cursor + sz) = unat data_cursor + unat sz"
    using no_overflow_data by (simp add: unat_word_ariths(1))
  have unat_tp_sz: "unat (tgt_pos + sz) = unat tgt_pos + unat sz"
    using no_overflow_tgt by (simp add: unat_word_ariths(1))
  \<comment> \<open>New data_rem: dropping further into the same take\<close>
  have new_data_rem: "drop (unat (data_cursor + sz))
      (take (unat data_end) (heap_bytes s0 patch patch_n))
    = drop (unat sz) (ds_data_rem dst)"
  proof -
    let ?xs = "take (unat data_end) (heap_bytes s0 patch patch_n)"
    have "drop (unat sz) (drop (unat data_cursor) ?xs) = drop (unat sz + unat data_cursor) ?xs"
      by (rule drop_drop)
    hence eq: "drop (unat data_cursor + unat sz) ?xs = drop (unat sz) (drop (unat data_cursor) ?xs)"
      by (simp add: add.commute)
    show ?thesis using eq unat_dc_sz dst_data by simp
  qed
  \<comment> \<open>New output: heap_bytes t' out (unat tgt_pos + unat sz)\<close>
  have new_tgt: "heap_bytes t' out (unat tgt_pos + unat sz)
    = ds_tgt dst @ take (unat sz) (ds_data_rem dst)"
  proof (rule nth_equalityI)
    show "length (heap_bytes t' out (unat tgt_pos + unat sz))
        = length (ds_tgt dst @ take (unat sz) (ds_data_rem dst))"
    proof -
      have "length (ds_tgt dst) = unat tgt_pos" using dst_tgt by simp
      moreover have "length (take (unat sz) (ds_data_rem dst)) = unat sz"
      proof -
        have "length (ds_data_rem dst) = unat data_end - unat data_cursor"
          using dst_data invD(10) invD(6) by (simp add: word_le_nat_alt)
        thus ?thesis using sz_fits_data by simp
      qed
      ultimately show ?thesis by simp
    qed
  next
    fix i assume i_bound: "i < length (heap_bytes t' out (unat tgt_pos + unat sz))"
    hence i_lt: "i < unat tgt_pos + unat sz" by simp
    show "heap_bytes t' out (unat tgt_pos + unat sz) ! i
        = (ds_tgt dst @ take (unat sz) (ds_data_rem dst)) ! i"
    proof (cases "i < unat tgt_pos")
      case True
      \<comment> \<open>Prefix: bytes already in output, preserved by out_prefix_preserved\<close>
      have lhs: "heap_bytes t' out (unat tgt_pos + unat sz) ! i
               = heap_w8 t' (out +\<^sub>p int i)"
        using i_lt by (simp add: heap_bytes_nth)
      have "heap_w8 t' (out +\<^sub>p int i) = heap_w8 t (out +\<^sub>p int i)"
        using out_prefix_preserved True by auto
      also have "... = heap_bytes t out (unat tgt_pos) ! i"
        using True by (simp add: heap_bytes_nth)
      also have "... = ds_tgt dst ! i" using dst_tgt by simp
      finally have "heap_bytes t' out (unat tgt_pos + unat sz) ! i = ds_tgt dst ! i"
        using lhs by simp
      moreover have "(ds_tgt dst @ take (unat sz) (ds_data_rem dst)) ! i = ds_tgt dst ! i"
        using True dst_tgt by (simp add: nth_append)
      ultimately show ?thesis by simp
    next
      case False
      hence i_ge: "unat tgt_pos \<le> i" by simp
      let ?j = "i - unat tgt_pos"
      have j_lt: "?j < unat sz" using i_lt i_ge by simp
      \<comment> \<open>New bytes: written by the ADD loop\<close>
      have lhs: "heap_bytes t' out (unat tgt_pos + unat sz) ! i
               = heap_w8 t' (out +\<^sub>p int i)"
        using i_lt by (simp add: heap_bytes_nth)
      have ptr_eq: "out +\<^sub>p int i = out +\<^sub>p uint (tgt_pos + of_nat ?j)"
      proof -
        have unat_eq: "unat (tgt_pos + of_nat ?j :: 32 word) = i"
        proof -
          have "unat tgt_pos + ?j = i" using i_ge by simp
          moreover have "i < 2 ^ 32" using i_lt no_overflow_tgt by simp
          ultimately show ?thesis
            by (simp add: unat_word_ariths(1) unat_of_nat)
        qed
        show ?thesis by (simp only: ptr_add_def uint_nat unat_eq of_int_of_nat_eq)
      qed
      have "heap_w8 t' (out +\<^sub>p uint (tgt_pos + of_nat ?j))
          = heap_w8 s0 (patch +\<^sub>p uint (data_cursor + of_nat ?j))"
        using add_result j_lt by auto
      \<comment> \<open>RHS: (ds_tgt dst @ take sz data_rem) ! i = data_rem ! j\<close>
      have rhs: "(ds_tgt dst @ take (unat sz) (ds_data_rem dst)) ! i
               = (take (unat sz) (ds_data_rem dst)) ! ?j"
        using i_ge dst_tgt by (simp add: nth_append)
      have data_rem_nth: "(take (unat sz) (ds_data_rem dst)) ! ?j
               = ds_data_rem dst ! ?j"
        using j_lt by simp
      have "ds_data_rem dst ! ?j =
            (drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n))) ! ?j"
        using dst_data by simp
      also have "... = (take (unat data_end) (heap_bytes s0 patch patch_n)) ! (unat data_cursor + ?j)"
      proof -
        have "unat data_cursor + ?j < unat data_end"
          using sz_fits_data j_lt invD(6) by (simp add: word_le_nat_alt)
        moreover have "length (take (unat data_end) (heap_bytes s0 patch patch_n)) = unat data_end"
          using invD(10) by simp
        ultimately show ?thesis by (simp add: nth_drop)
      qed
      also have "... = (heap_bytes s0 patch patch_n) ! (unat data_cursor + ?j)"
      proof -
        have idx_lt: "unat data_cursor + ?j < unat data_end"
          using sz_fits_data j_lt invD(6) by (simp add: word_le_nat_alt)
        thus ?thesis by (simp add: nth_take)
      qed
      also have "... = heap_w8 s0 (patch +\<^sub>p int (unat data_cursor + ?j))"
      proof -
        have "unat data_cursor + ?j < patch_n"
          using sz_fits_data j_lt invD(6) invD(10) by (simp add: word_le_nat_alt)
        thus ?thesis by (simp add: heap_bytes_nth)
      qed
      finally have data_byte: "ds_data_rem dst ! ?j
        = heap_w8 s0 (patch +\<^sub>p int (unat data_cursor + ?j))" .
      \<comment> \<open>Connect the patch pointer forms\<close>
      have patch_ptr_eq: "patch +\<^sub>p int (unat data_cursor + ?j)
                        = patch +\<^sub>p uint (data_cursor + of_nat ?j)"
      proof -
        have unat_eq: "unat (data_cursor + of_nat ?j :: 32 word) = unat data_cursor + ?j"
        proof -
          have "unat data_cursor + ?j < 2 ^ 32"
            using j_lt no_overflow_data by simp
          thus ?thesis by (simp add: unat_word_ariths(1) unat_of_nat)
        qed
        have "uint (data_cursor + of_nat ?j :: 32 word) = int (unat data_cursor + ?j)"
          by (simp only: uint_nat unat_eq)
        thus ?thesis by simp
      qed
      show ?thesis using lhs ptr_eq add_result[rule_format, OF j_lt]
        rhs data_rem_nth data_byte patch_ptr_eq by simp
    qed
  qed
  \<comment> \<open>cache_abs t' c np — arrays unchanged, so same as cache_abs t c np\<close>
  have cache_abs': "cache_abs t' c np"
    using cache_ok cache_preserved
    by (simp add: cache_abs_def)
  \<comment> \<open>code_tbl_matches t'\<close>
  have code_tbl': "code_tbl_matches t'"
    using invD(13) code_tbl_preserved by (simp add: code_tbl_matches_def)
  \<comment> \<open>buf_valid — depends only on heap_typing\<close>
  have bv_patch: "buf_valid t' patch patch_n"
    using invD(3) typing_preserved by (simp add: buf_valid_def)
  have bv_src: "buf_valid t' src src_n"
    using invD(4) typing_preserved by (simp add: buf_valid_def)
  have bv_out: "buf_valid t' out tgt_len"
    using invD(5) typing_preserved by (simp add: buf_valid_def)
  \<comment> \<open>heap_typing t' = heap_typing s0\<close>
  have typing_s0: "heap_typing t' = heap_typing s0"
    using typing_preserved invD(14) by simp
  \<comment> \<open>Cursor bound: data_cursor + sz \<le> data_end\<close>
  have dc_bound: "data_cursor + sz \<le> data_end"
  proof -
    have "unat data_cursor + unat sz \<le> unat data_end"
      using sz_fits_data invD(6) by (simp add: word_le_nat_alt)
    thus ?thesis using unat_dc_sz by (simp add: word_le_nat_alt)
  qed
  \<comment> \<open>tgt_pos bound\<close>
  have tp_bound: "unat (tgt_pos + sz) \<le> tgt_len"
    using sz_fits_tgt unat_tp_sz by simp
  \<comment> \<open>Now construct the new existential witness\<close>
  let ?new_dst = "dst \<lparr> ds_data_rem := drop (unat sz) (ds_data_rem dst),
                        ds_tgt := ds_tgt dst @ take (unat sz) (ds_data_rem dst) \<rparr>"
  show ?thesis
    unfolding decode_loop_inv_def
    apply (rule exI[where x = "?new_dst"])
    apply (rule exI[where x = c])
    apply (intro conjI)
    \<comment> \<open>ds_inst_rem: unchanged\<close>
    using dst_inst apply simp
    \<comment> \<open>ds_data_rem: advanced by sz\<close>
    using new_data_rem unat_dc_sz apply simp
    \<comment> \<open>ds_addr_rem: unchanged\<close>
    using dst_addr apply simp
    \<comment> \<open>ds_tgt: extended\<close>
    using new_tgt unat_tp_sz apply simp
    \<comment> \<open>ds_cache\<close>
    using dst_cache apply simp
    \<comment> \<open>cache_abs\<close>
    using cache_abs' apply simp
    \<comment> \<open>cache_wf\<close>
    using cwf apply simp
    \<comment> \<open>patch heap preserved\<close>
    using patch_preserved apply simp
    \<comment> \<open>src heap preserved\<close>
    using src_preserved apply simp
    \<comment> \<open>buf_valid patch\<close>
    using bv_patch apply simp
    \<comment> \<open>buf_valid src\<close>
    using bv_src apply simp
    \<comment> \<open>buf_valid out\<close>
    using bv_out apply simp
    \<comment> \<open>data_cursor + sz \<le> data_end\<close>
    using dc_bound apply simp
    \<comment> \<open>inst_cursor \<le> inst_end\<close>
    using invD(7) apply simp
    \<comment> \<open>addr_cursor \<le> addr_end\<close>
    using invD(8) apply simp
    \<comment> \<open>unat (tgt_pos + sz) \<le> tgt_len\<close>
    using tp_bound apply simp
    \<comment> \<open>unat data_end \<le> patch_n\<close>
    using invD(10) apply simp
    \<comment> \<open>unat inst_end \<le> patch_n\<close>
    using invD(11) apply simp
    \<comment> \<open>unat addr_end \<le> patch_n\<close>
    using invD(12) apply simp
    \<comment> \<open>code_tbl_matches\<close>
    using code_tbl' apply simp
    \<comment> \<open>heap_typing\<close>
    using typing_s0 apply simp
    \<comment> \<open>out/patch disjoint\<close>
    using invD(15) apply simp
    \<comment> \<open>out/src disjoint\<close>
    using invD(16) apply simp
    \<comment> \<open>out injectivity\<close>
    using invD(17) apply simp
    \<comment> \<open>tgt_len < 2^32\<close>
    using invD(18) apply simp
    \<comment> \<open>src_seg_off + src_seg_len \<le> src_n\<close>
    using invD(19) apply simp
    \<comment> \<open>src_seg_off + src_seg_len < 2^32\<close>
    using invD(20) apply simp
    \<comment> \<open>src_seg definition\<close>
    using invD(21) by simp
qed

(*
  RUN half-instruction: invariant preservation.
*)
lemma decode_loop_inv_after_run:
  fixes sz :: "32 word" and fill :: "8 word"
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
      and sz_pos: "0 < unat sz"
      and fill_read: "unat data_cursor < unat data_end"
      and sz_fits_tgt: "unat tgt_pos + unat sz \<le> tgt_len"
      and no_overflow_tgt: "unat tgt_pos + unat sz < 2 ^ 32"
      and no_overflow_data: "unat data_cursor + 1 < 2 ^ 32"
      \<comment> \<open>After the run loop\<close>
      and patch_preserved: "\<forall>j < patch_n. heap_w8 t' (patch +\<^sub>p int j) = heap_w8 s0 (patch +\<^sub>p int j)"
      and src_preserved: "\<forall>j < src_n. heap_w8 t' (src +\<^sub>p int j) = heap_w8 s0 (src +\<^sub>p int j)"
      and run_result: "\<forall>j < unat sz. heap_w8 t' (out +\<^sub>p uint (tgt_pos + of_nat j)) = fill"
      and fill_eq: "fill = heap_w8 s0 (patch +\<^sub>p int (unat data_cursor))"
      and out_prefix_preserved: "\<forall>i < unat tgt_pos. heap_w8 t' (out +\<^sub>p int i) = heap_w8 t (out +\<^sub>p int i)"
      and typing_preserved: "heap_typing t' = heap_typing t"
      and cache_preserved: "near_arr_'' t' = near_arr_'' t"
                           "same_arr_'' t' = same_arr_'' t"
      and code_tbl_preserved: "code_tbl_'' t' = code_tbl_'' t"
  shows "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           (data_cursor + 1) inst_cursor addr_cursor (tgt_pos + sz) np t'"
proof -
  note invD = decode_loop_invD[OF inv]
  obtain dst :: dec_state and c :: cache where
    dst_inst: "ds_inst_rem dst =
      drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))" and
    dst_data: "ds_data_rem dst =
      drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n))" and
    dst_addr: "ds_addr_rem dst =
      drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n))" and
    dst_tgt: "ds_tgt dst = heap_bytes t out (unat tgt_pos)" and
    dst_cache: "ds_cache dst = c" and
    cache_ok: "cache_abs t c np" and
    cwf: "cache_wf c"
    using inv unfolding decode_loop_inv_def by blast
  \<comment> \<open>Cursor arithmetic\<close>
  have unat_dc1: "unat (data_cursor + 1 :: 32 word) = unat data_cursor + 1"
    using no_overflow_data by (simp add: unat_word_ariths(1))
  have unat_tp_sz: "unat (tgt_pos + sz) = unat tgt_pos + unat sz"
    using no_overflow_tgt by (simp add: unat_word_ariths(1))
  \<comment> \<open>data_rem has at least one element (fill_read gives cursor < end)\<close>
  have data_rem_len: "length (ds_data_rem dst) = unat data_end - unat data_cursor"
    using dst_data invD(10) invD(6) by (simp add: word_le_nat_alt)
  have data_rem_nonempty: "0 < length (ds_data_rem dst)"
    using fill_read data_rem_len invD(6) by (simp add: word_le_nat_alt)
  \<comment> \<open>The fill byte is the head of ds_data_rem\<close>
  have fill_is_hd: "fill = hd (ds_data_rem dst)"
  proof -
    have "hd (ds_data_rem dst) = ds_data_rem dst ! 0"
      using data_rem_nonempty by (simp add: hd_conv_nth)
    also have "... = (drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n))) ! 0"
      using dst_data by simp
    also have "... = (take (unat data_end) (heap_bytes s0 patch patch_n)) ! (unat data_cursor)"
    proof -
      have "unat data_cursor < length (take (unat data_end) (heap_bytes s0 patch patch_n))"
        using fill_read invD(10) by simp
      thus ?thesis by (simp add: nth_drop)
    qed
    also have "... = (heap_bytes s0 patch patch_n) ! (unat data_cursor)"
      using fill_read by (simp add: nth_take)
    also have "... = heap_w8 s0 (patch +\<^sub>p int (unat data_cursor))"
    proof -
      have "unat data_cursor < patch_n" using fill_read invD(10) by simp
      thus ?thesis by (simp add: heap_bytes_nth)
    qed
    finally show ?thesis using fill_eq by simp
  qed
  \<comment> \<open>New data_rem: advance by 1\<close>
  have drop_tl: "\<And>n (xs :: 'z list). drop (Suc n) xs = tl (drop n xs)"
    by (simp add: drop_Suc tl_drop)
  have new_data_rem: "drop (unat (data_cursor + 1))
      (take (unat data_end) (heap_bytes s0 patch patch_n))
    = tl (ds_data_rem dst)"
  proof -
    let ?xs = "take (unat data_end) (heap_bytes s0 patch patch_n)"
    have eq1: "unat (data_cursor + 1 :: 32 word) = Suc (unat data_cursor)"
      using no_overflow_data unat_dc1 by simp
    have "drop (Suc (unat data_cursor)) ?xs = tl (drop (unat data_cursor) ?xs)"
      by (rule drop_tl)
    thus ?thesis using eq1 dst_data by simp
  qed
  \<comment> \<open>New output: heap_bytes t' out (unat tgt_pos + unat sz) = old_tgt @ replicate sz fill\<close>
  have new_tgt: "heap_bytes t' out (unat tgt_pos + unat sz)
    = ds_tgt dst @ replicate (unat sz) fill"
  proof (rule nth_equalityI)
    show "length (heap_bytes t' out (unat tgt_pos + unat sz))
        = length (ds_tgt dst @ replicate (unat sz) fill)"
      using dst_tgt by simp
  next
    fix i assume i_bound: "i < length (heap_bytes t' out (unat tgt_pos + unat sz))"
    hence i_lt: "i < unat tgt_pos + unat sz" by simp
    show "heap_bytes t' out (unat tgt_pos + unat sz) ! i
        = (ds_tgt dst @ replicate (unat sz) fill) ! i"
    proof (cases "i < unat tgt_pos")
      case True
      have "heap_bytes t' out (unat tgt_pos + unat sz) ! i = heap_w8 t' (out +\<^sub>p int i)"
        using i_lt by (simp add: heap_bytes_nth)
      also have "... = heap_w8 t (out +\<^sub>p int i)"
        using out_prefix_preserved True by auto
      also have "... = heap_bytes t out (unat tgt_pos) ! i"
        using True by (simp add: heap_bytes_nth)
      also have "... = ds_tgt dst ! i" using dst_tgt by simp
      finally show ?thesis using True dst_tgt by (simp add: nth_append)
    next
      case False
      hence i_ge: "unat tgt_pos \<le> i" by simp
      let ?j = "i - unat tgt_pos"
      have j_lt: "?j < unat sz" using i_lt i_ge by simp
      have "heap_bytes t' out (unat tgt_pos + unat sz) ! i = heap_w8 t' (out +\<^sub>p int i)"
        using i_lt by (simp add: heap_bytes_nth)
      also have "... = heap_w8 t' (out +\<^sub>p uint (tgt_pos + of_nat ?j))"
      proof -
        have unat_eq: "unat (tgt_pos + of_nat ?j :: 32 word) = i"
        proof -
          have "unat tgt_pos + ?j = i" using i_ge by simp
          moreover have "i < 2 ^ 32" using i_lt no_overflow_tgt by simp
          ultimately show ?thesis by (simp add: unat_word_ariths(1) unat_of_nat)
        qed
        show ?thesis by (simp only: ptr_add_def uint_nat unat_eq of_int_of_nat_eq)
      qed
      also have "... = fill" using run_result j_lt by auto
      finally have lhs: "heap_bytes t' out (unat tgt_pos + unat sz) ! i = fill" .
      have "(ds_tgt dst @ replicate (unat sz) fill) ! i = replicate (unat sz) fill ! ?j"
        using i_ge dst_tgt by (simp add: nth_append)
      also have "... = fill" using j_lt by simp
      finally show ?thesis using lhs by simp
    qed
  qed
  \<comment> \<open>cache_abs preserved\<close>
  have cache_abs': "cache_abs t' c np"
    using cache_ok cache_preserved by (simp add: cache_abs_def)
  have code_tbl': "code_tbl_matches t'"
    using invD(13) code_tbl_preserved by (simp add: code_tbl_matches_def)
  have bv_patch: "buf_valid t' patch patch_n"
    using invD(3) typing_preserved by (simp add: buf_valid_def)
  have bv_src: "buf_valid t' src src_n"
    using invD(4) typing_preserved by (simp add: buf_valid_def)
  have bv_out: "buf_valid t' out tgt_len"
    using invD(5) typing_preserved by (simp add: buf_valid_def)
  have typing_s0: "heap_typing t' = heap_typing s0"
    using typing_preserved invD(14) by simp
  \<comment> \<open>data_cursor + 1 \<le> data_end\<close>
  have dc_bound: "data_cursor + 1 \<le> data_end"
  proof -
    have "unat data_cursor + 1 \<le> unat data_end"
      using fill_read by simp
    thus ?thesis using unat_dc1 by (simp add: word_le_nat_alt)
  qed
  have tp_bound: "unat (tgt_pos + sz) \<le> tgt_len"
    using sz_fits_tgt unat_tp_sz by simp
  \<comment> \<open>Construct witness: data_rem becomes tl, tgt gets replicated fill\<close>
  let ?new_dst = "dst \<lparr> ds_data_rem := tl (ds_data_rem dst),
                        ds_tgt := ds_tgt dst @ replicate (unat sz) fill \<rparr>"
  show ?thesis
    unfolding decode_loop_inv_def
    apply (rule exI[where x = "?new_dst"])
    apply (rule exI[where x = c])
    apply (intro conjI)
    using dst_inst apply simp
    using new_data_rem unat_dc1 apply simp
    using dst_addr apply simp
    using new_tgt unat_tp_sz apply simp
    using dst_cache apply simp
    using cache_abs' apply simp
    using cwf apply simp
    using patch_preserved apply simp
    using src_preserved apply simp
    using bv_patch apply simp
    using bv_src apply simp
    using bv_out apply simp
    using dc_bound apply simp
    using invD(7) apply simp
    using invD(8) apply simp
    using tp_bound apply simp
    using invD(10) apply simp
    using invD(11) apply simp
    using invD(12) apply simp
    using code_tbl' apply simp
    using typing_s0 apply simp
    using invD(15) apply simp
    using invD(16) apply simp
    using invD(17) apply simp
    using invD(18) apply simp
    using invD(19) apply simp
    using invD(20) apply simp
    using invD(21) by simp
qed

(*
  COPY half-instruction: invariant preservation.
  After decode_address' gives us (addr, new_np, new_addr_cursor) and
  copy_loop_correct copies sz bytes.
*)
lemma decode_loop_inv_after_copy:
  fixes sz :: "32 word" and addr :: "32 word" and new_np :: "32 word"
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
      and sz_pos: "0 < unat sz"
      and sz_fits_tgt: "unat tgt_pos + unat sz \<le> tgt_len"
      and no_overflow_tgt: "unat tgt_pos + unat sz < 2 ^ 32"
      and addr_ok: "unat addr < unat src_seg_len + unat tgt_pos"
      and new_addr_cursor_ok: "new_addr_cursor \<le> addr_end"
      \<comment> \<open>After decode_address' + copy loop\<close>
      and patch_preserved: "\<forall>j < patch_n. heap_w8 t' (patch +\<^sub>p int j) = heap_w8 s0 (patch +\<^sub>p int j)"
      and src_preserved: "\<forall>j < src_n. heap_w8 t' (src +\<^sub>p int j) = heap_w8 s0 (src +\<^sub>p int j)"
      and copy_result: "\<forall>k < unat sz.
             heap_w8 t' (out +\<^sub>p uint (tgt_pos + of_nat k)) =
             copy_loop src_seg (heap_bytes t out (unat tgt_pos)) (unat addr) (unat sz)
               ! (unat tgt_pos + k)"
      and out_prefix_preserved: "\<forall>i < unat tgt_pos. heap_w8 t' (out +\<^sub>p int i) = heap_w8 t (out +\<^sub>p int i)"
      and typing_preserved: "heap_typing t' = heap_typing t"
      and cache_updated: "cache_abs t' c' new_np"
      and cache_wf': "cache_wf c'"
      and np_bound: "unat new_np < s_near"
      and code_tbl_preserved: "code_tbl_'' t' = code_tbl_'' t"
  shows "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           data_cursor inst_cursor new_addr_cursor (tgt_pos + sz) new_np t'"
proof -
  note invD = decode_loop_invD[OF inv]
  obtain dst :: dec_state and c :: cache where
    dst_inst: "ds_inst_rem dst =
      drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))" and
    dst_data: "ds_data_rem dst =
      drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n))" and
    dst_addr: "ds_addr_rem dst =
      drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n))" and
    dst_tgt: "ds_tgt dst = heap_bytes t out (unat tgt_pos)" and
    dst_cache: "ds_cache dst = c" and
    cache_ok: "cache_abs t c np" and
    cwf: "cache_wf c"
    using inv unfolding decode_loop_inv_def by blast
  \<comment> \<open>Cursor arithmetic\<close>
  have unat_tp_sz: "unat (tgt_pos + sz) = unat tgt_pos + unat sz"
    using no_overflow_tgt by (simp add: unat_word_ariths(1))
  \<comment> \<open>The copy_loop result\<close>
  let ?cl = "copy_loop src_seg (ds_tgt dst) (unat addr) (unat sz)"
  have cl_len: "length ?cl = unat tgt_pos + unat sz"
    using dst_tgt by (simp add: copy_loop_length)
  \<comment> \<open>New output matches copy_loop\<close>
  have new_tgt: "heap_bytes t' out (unat tgt_pos + unat sz) = ?cl"
  proof (rule nth_equalityI)
    show "length (heap_bytes t' out (unat tgt_pos + unat sz)) = length ?cl"
      using cl_len by simp
  next
    fix i assume i_bound: "i < length (heap_bytes t' out (unat tgt_pos + unat sz))"
    hence i_lt: "i < unat tgt_pos + unat sz" by simp
    show "heap_bytes t' out (unat tgt_pos + unat sz) ! i = ?cl ! i"
    proof (cases "i < unat tgt_pos")
      case True
      have "heap_bytes t' out (unat tgt_pos + unat sz) ! i = heap_w8 t' (out +\<^sub>p int i)"
        using i_lt by (simp add: heap_bytes_nth)
      also have "... = heap_w8 t (out +\<^sub>p int i)"
        using out_prefix_preserved True by auto
      also have "... = heap_bytes t out (unat tgt_pos) ! i"
        using True by (simp add: heap_bytes_nth)
      also have "... = ds_tgt dst ! i" using dst_tgt by simp
      also have "... = ?cl ! i"
      proof -
        have "i < length (ds_tgt dst)" using True dst_tgt by simp
        thus ?thesis using copy_loop_prefix by simp
      qed
      finally show ?thesis .
    next
      case False
      hence i_ge: "unat tgt_pos \<le> i" by simp
      let ?k = "i - unat tgt_pos"
      have k_lt: "?k < unat sz" using i_lt i_ge by simp
      have "heap_bytes t' out (unat tgt_pos + unat sz) ! i = heap_w8 t' (out +\<^sub>p int i)"
        using i_lt by (simp add: heap_bytes_nth)
      also have "... = heap_w8 t' (out +\<^sub>p uint (tgt_pos + of_nat ?k))"
      proof -
        have unat_eq: "unat (tgt_pos + of_nat ?k :: 32 word) = i"
        proof -
          have "unat tgt_pos + ?k = i" using i_ge by simp
          moreover have "i < 2 ^ 32" using i_lt no_overflow_tgt by simp
          ultimately show ?thesis by (simp add: unat_word_ariths(1) unat_of_nat)
        qed
        show ?thesis by (simp only: ptr_add_def uint_nat unat_eq of_int_of_nat_eq)
      qed
      also have "... = copy_loop src_seg (heap_bytes t out (unat tgt_pos))
                         (unat addr) (unat sz) ! (unat tgt_pos + ?k)"
        using copy_result k_lt by auto
      also have "... = ?cl ! (unat tgt_pos + ?k)"
        using dst_tgt by simp
      also have "unat tgt_pos + ?k = i" using i_ge by simp
      finally show ?thesis by simp
    qed
  qed
  \<comment> \<open>Preserved invariant fields\<close>
  have code_tbl': "code_tbl_matches t'"
    using invD(13) code_tbl_preserved by (simp add: code_tbl_matches_def)
  have bv_patch: "buf_valid t' patch patch_n"
    using invD(3) typing_preserved by (simp add: buf_valid_def)
  have bv_src: "buf_valid t' src src_n"
    using invD(4) typing_preserved by (simp add: buf_valid_def)
  have bv_out: "buf_valid t' out tgt_len"
    using invD(5) typing_preserved by (simp add: buf_valid_def)
  have typing_s0: "heap_typing t' = heap_typing s0"
    using typing_preserved invD(14) by simp
  have tp_bound: "unat (tgt_pos + sz) \<le> tgt_len"
    using sz_fits_tgt unat_tp_sz by simp
  \<comment> \<open>Construct witness\<close>
  let ?new_dst = "dst \<lparr> ds_addr_rem := drop (unat new_addr_cursor)
                          (take (unat addr_end) (heap_bytes s0 patch patch_n)),
                        ds_cache := c',
                        ds_tgt := ?cl \<rparr>"
  show ?thesis
    unfolding decode_loop_inv_def
    apply (rule exI[where x = "?new_dst"])
    apply (rule exI[where x = c'])
    apply (intro conjI)
    \<comment> \<open>ds_inst_rem\<close>
    using dst_inst apply simp
    \<comment> \<open>ds_data_rem\<close>
    using dst_data apply simp
    \<comment> \<open>ds_addr_rem\<close>
    apply simp
    \<comment> \<open>ds_tgt\<close>
    using new_tgt unat_tp_sz apply simp
    \<comment> \<open>ds_cache\<close>
    apply simp
    \<comment> \<open>cache_abs\<close>
    using cache_updated apply simp
    \<comment> \<open>cache_wf\<close>
    using cache_wf' apply simp
    \<comment> \<open>patch preserved\<close>
    using patch_preserved apply simp
    \<comment> \<open>src preserved\<close>
    using src_preserved apply simp
    \<comment> \<open>buf_valid\<close>
    using bv_patch apply simp
    using bv_src apply simp
    using bv_out apply simp
    \<comment> \<open>cursor bounds\<close>
    using invD(6) apply simp
    using invD(7) apply simp
    using new_addr_cursor_ok apply simp
    using tp_bound apply simp
    \<comment> \<open>end bounds\<close>
    using invD(10) apply simp
    using invD(11) apply simp
    using invD(12) apply simp
    \<comment> \<open>code_tbl, typing, disjoint, etc\<close>
    using code_tbl' apply simp
    using typing_s0 apply simp
    using invD(15) apply simp
    using invD(16) apply simp
    using invD(17) apply simp
    using invD(18) apply simp
    using invD(19) apply simp
    using invD(20) apply simp
    using invD(21) by simp
qed

(*
  Full C-side prefix refinement: the C decoder reaches the main while-loop
  with cursors matching parse_window, for the no-source, no-app, built case.

  This is the "success path prefix": under the assumptions that parse_header
  and parse_window both succeed, the C function reaches the main loop with
  the correct cursor positions. The main loop invariant then takes over.

  Strategy: unfold vcdiff_decode'_def, runs_to_vcg through the prefix,
  discharge each VCG subgoal using init loop lemmas and read_varint'_chain.

  The postcondition says the C reaches a Result (not an early return error).
  A more detailed version establishing cursor positions will come later,
  once the main-loop invariant structure is defined.
*)

lemma word_less_trans_le:
  fixes x :: "'a::len word"
  assumes "x < y" and "y \<le> z"
  shows "x < z"
  using assms by (meson order.strict_trans2)

lemma inst_end_le_patch_len:
  fixes pos_v pos_vd val_v val_vb val_vc val_vd patch_len :: "32 word"
  assumes sizes: "val_v - (pos_vd - pos_v) = val_vb + val_vc + val_vd"
    and dlen_fit: "\<not> unat (patch_len - pos_v) < unat val_v"
    and pos_v_le: "pos_v \<le> patch_len"
    and vd_le_v: "val_vd \<le> val_v"
  shows "pos_vd + val_vb + val_vc \<le> patch_len"
proof -
  have sum_full: "pos_vd + val_vb + val_vc + val_vd = pos_v + val_v"
    using sizes by (simp add: algebra_simps)
  have sub_eq: "pos_vd + val_vb + val_vc = pos_v + val_v - val_vd"
    by (metis sum_full add_diff_cancel_right')
  have sum_le: "unat pos_v + unat val_v \<le> unat patch_len"
  proof -
    have "unat (patch_len - pos_v) = unat patch_len - unat pos_v"
      using pos_v_le by (simp add: unat_sub word_le_nat_alt)
    hence "unat val_v \<le> unat patch_len - unat pos_v"
      using dlen_fit by simp
    thus ?thesis using pos_v_le by (simp add: word_le_nat_alt)
  qed
  have unat_pv: "unat (pos_v + val_v) = unat pos_v + unat val_v"
    using sum_le unat_lt2p[of patch_len]
    by (simp add: unat_add_lem[THEN iffD1])
  have pv_le: "pos_v + val_v \<le> patch_len"
    using sum_le unat_pv by (simp add: word_le_nat_alt)
  have vd_le_pv: "val_vd \<le> pos_v + val_v"
    using vd_le_v unat_pv by (simp add: word_le_nat_alt)
  show ?thesis using sub_eq vd_le_pv pv_le
    by (metis word_sub_le order.trans)
qed

lemma inst_end_le_patch_len2:
  fixes pos_vd val_vb val_vc patch_len :: "32 word"
  assumes pos_vd_eq: "unat pos_vd = unat patch_len - rest_len"
    and rest_bound: "rest_len \<le> unat patch_len"
    and sizes_fit: "unat val_vb + unat val_vc + addr_n \<le> rest_len"
  shows "unat (pos_vd + val_vb + val_vc) \<le> unat patch_len"
proof -
  have sum_nat: "unat val_vb + unat val_vc \<le> rest_len"
    using sizes_fit by linarith
  have nat_bound: "unat pos_vd + unat val_vb + unat val_vc \<le> unat patch_len"
    using pos_vd_eq rest_bound sum_nat by linarith
  have no_overflow: "unat pos_vd + unat val_vb + unat val_vc < 4294967296"
    using nat_bound unat_lt2p[of patch_len] by simp
  have "unat (pos_vd + val_vb) = unat pos_vd + unat val_vb"
    using no_overflow by (simp add: unat_add_lem[THEN iffD1])
  moreover have "unat (pos_vd + val_vb + val_vc) = unat pos_vd + unat val_vb + unat val_vc"
    using no_overflow calculation by (simp add: unat_add_lem[THEN iffD1])
  ultimately show ?thesis using nat_bound by simp
qed

lemma inst_end_le_patch_len3:
  fixes pos_vd val_vb val_vc val_vd patch_len :: "32 word"
  assumes "unat pos_vd = unat patch_len - rest_len"
    and "rest_len \<le> unat patch_len"
    and "unat val_vb + unat val_vc + unat val_vd \<le> rest_len"
  shows "unat (pos_vd + val_vb + val_vc) \<le> unat patch_len"
  using inst_end_le_patch_len2[OF assms] .


lemma inst_end_le_word:
  fixes pos_vd val_vb val_vc patch_len :: "32 word"
  assumes pos_vd_le: "pos_vd \<le> patch_len"
    and sizes_fit: "unat val_vb + unat val_vc + unat val_vd \<le> unat patch_len - unat pos_vd"
  shows "pos_vd + val_vb + val_vc \<le> patch_len"
proof -
  have nat_bound: "unat pos_vd + unat val_vb + unat val_vc \<le> unat patch_len"
    using pos_vd_le sizes_fit by (simp add: word_le_nat_alt)
  have no_overflow: "unat pos_vd + unat val_vb + unat val_vc < 4294967296"
    using nat_bound unat_lt2p[of patch_len] by simp
  have "unat (pos_vd + val_vb) = unat pos_vd + unat val_vb"
    using no_overflow by (simp add: unat_add_lem[THEN iffD1])
  moreover have "unat (pos_vd + val_vb + val_vc) = unat pos_vd + unat val_vb + unat val_vc"
    using no_overflow calculation by (simp add: unat_add_lem[THEN iffD1])
  ultimately show ?thesis using nat_bound by (simp add: word_le_nat_alt)
qed

lemma word_le_of_unat_le:
  fixes a b :: "'a::len word"
  assumes "unat a \<le> unat b"
  shows "a \<le> b"
  using assms by (simp add: word_le_nat_alt)

lemma pos_chain_le:
  fixes pos_v pos_vd patch_len :: "32 word"
  assumes "unat pos_v = unat patch_len - lv"
    and "unat pos_vd = unat patch_len - ld"
    and "ld \<le> lv"
  shows "pos_v \<le> pos_vd"
  using assms by (simp add: word_le_nat_alt)

(*
  Invariant preservation after inst_cursor advance (opcode read).
  When we read one byte from inst_cursor, the invariant is preserved
  with inst_cursor+1 (ds_inst_rem drops one byte).
*)
lemma decode_loop_inv_advance_inst:
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
      and ic_lt: "unat inst_cursor < unat inst_end"
      and no_overflow: "unat inst_cursor + 1 < 2 ^ 32"
  shows "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           data_cursor (inst_cursor + 1) addr_cursor tgt_pos np t"
proof -
  note invD = decode_loop_invD[OF inv]
  obtain dst :: dec_state and c :: cache where
    dst_inst: "ds_inst_rem dst =
      drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))" and
    dst_data: "ds_data_rem dst =
      drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n))" and
    dst_addr: "ds_addr_rem dst =
      drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n))" and
    dst_tgt: "ds_tgt dst = heap_bytes t out (unat tgt_pos)" and
    dst_cache: "ds_cache dst = c" and
    cache_ok: "cache_abs t c np" and
    cwf: "cache_wf c"
    using inv unfolding decode_loop_inv_def by blast
  have unat_ic1: "unat (inst_cursor + 1 :: 32 word) = Suc (unat inst_cursor)"
    using no_overflow by (simp add: unat_word_ariths(1))
  have ic1_le: "inst_cursor + 1 \<le> inst_end"
  proof -
    have "Suc (unat inst_cursor) \<le> unat inst_end" using ic_lt by simp
    thus ?thesis using unat_ic1 by (simp add: word_le_nat_alt)
  qed
  \<comment> \<open>New inst_rem drops one more byte\<close>
  have new_inst: "drop (unat (inst_cursor + 1))
      (take (unat inst_end) (heap_bytes s0 patch patch_n))
    = tl (ds_inst_rem dst)"
  proof -
    have drop_tl: "\<And>n (xs :: 'z list). drop (Suc n) xs = tl (drop n xs)"
      by (simp add: drop_Suc tl_drop)
    have "drop (Suc (unat inst_cursor))
        (take (unat inst_end) (heap_bytes s0 patch patch_n))
      = tl (drop (unat inst_cursor)
        (take (unat inst_end) (heap_bytes s0 patch patch_n)))"
      by (rule drop_tl)
    thus ?thesis using unat_ic1 dst_inst by simp
  qed
  \<comment> \<open>Construct new witness with inst_rem = tl (old inst_rem)\<close>
  let ?new_dst = "dst \<lparr> ds_inst_rem := tl (ds_inst_rem dst) \<rparr>"
  show ?thesis
    unfolding decode_loop_inv_def
    apply (rule exI[where x = "?new_dst"])
    apply (rule exI[where x = c])
    apply (intro conjI)
    using new_inst apply simp
    using dst_data apply simp
    using dst_addr apply simp
    using dst_tgt apply simp
    using dst_cache apply simp
    using cache_ok apply simp
    using cwf apply simp
    using invD(1) apply simp
    using invD(2) apply simp
    using invD(3) apply simp
    using invD(4) apply simp
    using invD(5) apply simp
    using invD(6) apply simp
    using ic1_le apply simp
    using invD(8) apply simp
    using invD(9) apply simp
    using invD(10) apply simp
    using invD(11) apply simp
    using invD(12) apply simp
    using invD(13) apply simp
    using invD(14) apply simp
    using invD(15) apply simp
    using invD(16) apply simp
    using invD(17) apply simp
    using invD(18) apply simp
    using invD(19) apply simp
    using invD(20) apply simp
    using invD(21) by simp
qed

(*
  General invariant preservation: advance inst_cursor by n (for varint reads).
  The invariant is preserved with inst_cursor + of_nat n, dropping n from inst_rem.
*)
lemma decode_loop_inv_advance_inst_n:
  fixes n :: nat
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
      and n_fits: "unat inst_cursor + n \<le> unat inst_end"
      and no_overflow: "unat inst_cursor + n < 2 ^ 32"
  shows "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
           data_end inst_end addr_end src_seg
           data_cursor (inst_cursor + of_nat n) addr_cursor tgt_pos np t"
proof -
  note invD = decode_loop_invD[OF inv]
  obtain dst :: dec_state and c :: cache where
    dst_inst: "ds_inst_rem dst =
      drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))" and
    dst_data: "ds_data_rem dst =
      drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n))" and
    dst_addr: "ds_addr_rem dst =
      drop (unat addr_cursor) (take (unat addr_end) (heap_bytes s0 patch patch_n))" and
    dst_tgt: "ds_tgt dst = heap_bytes t out (unat tgt_pos)" and
    dst_cache: "ds_cache dst = c" and
    cache_ok: "cache_abs t c np" and
    cwf: "cache_wf c"
    using inv unfolding decode_loop_inv_def by blast
  have unat_icn: "unat (inst_cursor + of_nat n :: 32 word) = unat inst_cursor + n"
    using no_overflow by (simp add: unat_word_ariths(1) unat_of_nat)
  have icn_le: "inst_cursor + of_nat n \<le> inst_end"
    using n_fits unat_icn by (simp add: word_le_nat_alt)
  have new_inst: "drop (unat (inst_cursor + of_nat n))
      (take (unat inst_end) (heap_bytes s0 patch patch_n))
    = drop n (ds_inst_rem dst)"
  proof -
    let ?xs = "take (unat inst_end) (heap_bytes s0 patch patch_n)"
    have "drop n (drop (unat inst_cursor) ?xs) = drop (n + unat inst_cursor) ?xs"
      by (rule drop_drop)
    thus ?thesis using unat_icn dst_inst by (simp add: add.commute)
  qed
  let ?new_dst = "dst \<lparr> ds_inst_rem := drop n (ds_inst_rem dst) \<rparr>"
  show ?thesis
    unfolding decode_loop_inv_def
    apply (rule exI[where x = "?new_dst"])
    apply (rule exI[where x = c])
    apply (intro conjI)
    using new_inst apply simp
    using dst_data apply simp
    using dst_addr apply simp
    using dst_tgt apply simp
    using dst_cache apply simp
    using cache_ok apply simp
    using cwf apply simp
    using invD(1) apply simp
    using invD(2) apply simp
    using invD(3) apply simp
    using invD(4) apply simp
    using invD(5) apply simp
    using invD(6) apply simp
    using icn_le apply simp
    using invD(8) apply simp
    using invD(9) apply simp
    using invD(10) apply simp
    using invD(11) apply simp
    using invD(12) apply simp
    using invD(13) apply simp
    using invD(14) apply simp
    using invD(15) apply simp
    using invD(16) apply simp
    using invD(17) apply simp
    using invD(18) apply simp
    using invD(19) apply simp
    using invD(20) apply simp
    using invD(21) by simp
qed

(*
  buf_valid is monotone: if all pointers in [0..n) are valid and m \<le> n,
  then all pointers in [0..m) are valid.
*)
lemma buf_valid_mono:
  assumes "buf_valid s buf n" and "m \<le> n"
  shows "buf_valid s buf m"
  using assms by (auto simp: buf_valid_def)

(*
  Under the invariant, reading a varint from the inst section corresponds
  to varint_decode on ds_inst_rem. This bridges read_varint'_spec
  (which operates on heap_bytes s0 patch (unat inst_end) from inst_cursor)
  with the abstract ds_inst_rem in the invariant.

  Key fact: ds_inst_rem = drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))
  and read_varint' operates on drop (unat inst_cursor) (heap_bytes t patch (unat inst_end)).
  These are equal because:
    - heap_bytes t patch (unat inst_end) = take (unat inst_end) (heap_bytes t patch patch_n)
      (by take/map commutation when unat inst_end \<le> patch_n)
    - heap_bytes t patch k = heap_bytes s0 patch k (patch heap unchanged)
*)
lemma inv_inst_varint_bridge:
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
  shows "drop (unat inst_cursor) (heap_bytes t patch (unat inst_end))
       = drop (unat inst_cursor) (take (unat inst_end) (heap_bytes s0 patch patch_n))"
proof -
  note invD = decode_loop_invD[OF inv]
  have ie_le: "unat inst_end \<le> patch_n" using invD(11) .
  have patch_eq: "\<forall>i < patch_n. heap_w8 t (patch +\<^sub>p int i) = heap_w8 s0 (patch +\<^sub>p int i)"
    using invD(1) .
  have "heap_bytes t patch (unat inst_end) = take (unat inst_end) (heap_bytes s0 patch patch_n)"
  proof (rule nth_equalityI)
    show "length (heap_bytes t patch (unat inst_end))
        = length (take (unat inst_end) (heap_bytes s0 patch patch_n))"
      using ie_le by simp
  next
    fix i assume "i < length (heap_bytes t patch (unat inst_end))"
    hence i_lt: "i < unat inst_end" by simp
    have "heap_bytes t patch (unat inst_end) ! i = heap_w8 t (patch +\<^sub>p int i)"
      using i_lt by (simp add: heap_bytes_nth)
    also have "... = heap_w8 s0 (patch +\<^sub>p int i)"
      using patch_eq i_lt ie_le by auto
    also have "... = heap_bytes s0 patch patch_n ! i"
    proof -
      have "i < patch_n" using i_lt ie_le by simp
      thus ?thesis by (simp add: heap_bytes_nth)
    qed
    also have "... = take (unat inst_end) (heap_bytes s0 patch patch_n) ! i"
      using i_lt by (simp add: nth_take)
    finally show "heap_bytes t patch (unat inst_end) ! i
               = take (unat inst_end) (heap_bytes s0 patch patch_n) ! i" .
  qed
  thus ?thesis by simp
qed

(*
  Under code_tbl_matches, the first half-instruction from code_tbl[op] has:
  - typ (slot 0): corresponds to ity of fst (default_entry op)
  - sz  (slot 1): corresponds to isz of fst (default_entry op)
  - md  (slot 2): mode (only used for COPY)
  And byte_to_hi of these three gives fst (default_entry op).
*)
lemma code_tbl_matches_first_half:
  assumes "code_tbl_matches t"
      and "unat (op :: 8 word) < 256"
  shows "byte_to_hi (code_tbl_'' t .[unat op] .[0])
                    (code_tbl_'' t .[unat op] .[1])
                    (code_tbl_'' t .[unat op] .[2])
       = fst (default_entry (unat op))"
proof -
  let ?row = "code_tbl_'' t .[unat op]"
  have eq: "(byte_to_hi (?row.[0]) (?row.[1]) (?row.[2]),
             byte_to_hi (?row.[3]) (?row.[4]) (?row.[5]))
          = default_entry (unat op)"
    using code_tbl_matches_lookup[OF assms] by (simp add: entry_of_row_def)
  have "fst (byte_to_hi (?row.[0]) (?row.[1]) (?row.[2]),
             byte_to_hi (?row.[3]) (?row.[4]) (?row.[5]))
      = fst (default_entry (unat op))"
    using eq by simp
  thus ?thesis by simp
qed

lemma code_tbl_matches_second_half:
  assumes "code_tbl_matches t"
      and "unat (op :: 8 word) < 256"
  shows "byte_to_hi (code_tbl_'' t .[unat op] .[3])
                    (code_tbl_'' t .[unat op] .[4])
                    (code_tbl_'' t .[unat op] .[5])
       = snd (default_entry (unat op))"
proof -
  let ?row = "code_tbl_'' t .[unat op]"
  have eq: "(byte_to_hi (?row.[0]) (?row.[1]) (?row.[2]),
             byte_to_hi (?row.[3]) (?row.[4]) (?row.[5]))
          = default_entry (unat op)"
    using code_tbl_matches_lookup[OF assms] by (simp add: entry_of_row_def)
  have "snd (byte_to_hi (?row.[0]) (?row.[1]) (?row.[2]),
             byte_to_hi (?row.[3]) (?row.[4]) (?row.[5]))
      = snd (default_entry (unat op))"
    using eq by simp
  thus ?thesis by simp
qed

(*
  Key bridge lemma: the C's check "typ == 0" corresponds to ity h = NOOP,
  "typ == 1" to IADD, "typ == 2" to IRUN, "typ >= 3" to ICOPY.
  This follows from byte_to_hi's definition.
*)
lemma byte_to_hi_tag_ity:
  "ity (byte_to_hi tag sz mode) =
     (if tag = 0 then NOOP
      else if tag = 1 then IADD
      else if tag = 2 then IRUN
      else if tag = 3 then ICOPY (unat mode)
      else NOOP)"
  by (simp add: byte_to_hi_def noop_hi_def add_hi_def run_hi_def copy_hi_def)

lemma byte_to_hi_tag_isz:
  "isz (byte_to_hi tag sz mode) =
     (if tag = 0 then 0
      else if tag = 1 \<or> tag = 2 \<or> tag = 3 then unat sz
      else 0)"
  by (simp add: byte_to_hi_def noop_hi_def add_hi_def run_hi_def copy_hi_def)

(*
  Overflow safety under the invariant: if sz fits within the data section
  (sz \<le> data_end - data_cursor) and the data section ends within patch,
  then there's no overflow in data_cursor + sz.
*)
lemma inv_no_overflow_data:
  fixes data_cursor :: "32 word" and data_end :: "32 word" and sz :: "32 word"
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
      and sz_fits: "unat sz \<le> unat data_end - unat data_cursor"
  shows "unat data_cursor + unat sz < 2 ^ 32"
proof -
  note invD = decode_loop_invD[OF inv]
  have bd: "unat data_cursor + unat sz \<le> unat data_end"
    using sz_fits invD(6) by (simp add: word_le_nat_alt)
  have "unat (data_end :: 32 word) < 2 ^ 32"
    using unat_lt2p[where x = data_end] by simp
  thus ?thesis using bd by simp
qed

(*
  Overflow safety for tgt: if tgt_pos + sz \<le> tgt_len and tgt_len < 2^32,
  then tgt_pos + sz doesn't overflow.
*)
lemma inv_no_overflow_tgt:
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
      and sz_fits: "unat tgt_pos + unat sz \<le> tgt_len"
  shows "unat tgt_pos + unat sz < 2 ^ 32"
proof -
  note invD = decode_loop_invD[OF inv]
  have "unat tgt_pos + unat sz \<le> tgt_len" using sz_fits .
  also have "tgt_len < 2 ^ 32" using invD(18) .
  finally show ?thesis .
qed

(*
  resolve_size always returns a suffix: length rest \<le> length bs.
*)
lemma resolve_size_length:
  assumes "resolve_size h bs = Some (sz, rest)"
  shows "length rest \<le> length bs"
  using assms varint_decode_length
  by (auto simp: resolve_size_def split: if_splits)

(*
  resolve_size with non-zero isz returns the input unchanged.
*)
lemma resolve_size_nonzero:
  assumes "isz h \<noteq> 0 \<or> ity h = NOOP"
  shows "resolve_size h bs = Some (isz h, bs)"
  using assms by (auto simp: resolve_size_def)

(*
  resolve_size with zero isz and non-NOOP delegates to varint_decode.
*)
lemma resolve_size_varint:
  assumes "isz h = 0" and "ity h \<noteq> NOOP"
  shows "resolve_size h bs = varint_decode bs"
  using assms by (simp add: resolve_size_def)

(*
  Under the invariant, the length of ds_data_rem equals data_end - data_cursor.
  This connects the C's bounds check (sz > data_end - data_cursor) to the
  spec's check (sz > length (ds_data_rem st)).
*)
lemma inv_data_rem_length:
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
  shows "length (drop (unat data_cursor) (take (unat data_end) (heap_bytes s0 patch patch_n)))
       = unat data_end - unat data_cursor"
proof -
  note invD = decode_loop_invD[OF inv]
  show ?thesis using invD(10) invD(6) by (simp add: word_le_nat_alt)
qed

lemma inv_tgt_length:
  assumes inv: "decode_loop_inv s0 patch patch_n src src_n out src_seg_off src_seg_len tgt_len
                  data_end inst_end addr_end src_seg
                  data_cursor inst_cursor addr_cursor tgt_pos np t"
  shows "length (heap_bytes t out (unat tgt_pos)) = unat tgt_pos"
  by simp


(*
  When exec_half for IADD succeeds on the abstract state, the numeric
  conditions match what the C needs for the ADD dispatch.
  Specifically: sz \<le> length data_rem and tgt_pos + sz \<le> tgt_len.
*)
lemma exec_half_add_conditions:
  assumes "ity h = IADD"
      and "exec_half h sz src_seg src_seg_len tgt_len st = Inl st'"
  shows "sz \<le> length (ds_data_rem st)"
    and "length (ds_tgt st) + sz \<le> tgt_len"
    and "ds_data_rem st' = drop sz (ds_data_rem st)"
    and "ds_tgt st' = ds_tgt st @ take sz (ds_data_rem st)"
    and "ds_inst_rem st' = ds_inst_rem st"
    and "ds_addr_rem st' = ds_addr_rem st"
    and "ds_cache st' = ds_cache st"
  using assms by (auto simp: exec_half_def split: if_splits)

lemma exec_half_run_conditions:
  assumes "ity h = IRUN"
      and "exec_half h sz src_seg src_seg_len tgt_len st = Inl st'"
  shows "ds_data_rem st \<noteq> []"
    and "length (ds_tgt st) + sz \<le> tgt_len"
    and "ds_data_rem st' = tl (ds_data_rem st)"
    and "ds_tgt st' = ds_tgt st @ replicate sz (hd (ds_data_rem st))"
    and "ds_inst_rem st' = ds_inst_rem st"
    and "ds_addr_rem st' = ds_addr_rem st"
    and "ds_cache st' = ds_cache st"
  using assms by (auto simp: exec_half_def pop_byte_def split: if_splits list.splits)

lemma exec_half_noop:
  assumes "ity h = NOOP"
  shows "exec_half h sz src_seg src_seg_len tgt_len st = Inl st"
  using assms by (simp add: exec_half_def)

lemma exec_half_copy_conditions:
  assumes "ity h = ICOPY mode"
      and "exec_half h sz src_seg src_seg_len tgt_len st = Inl st'"
  shows "\<exists>addr rest c'.
           decode_address (ds_cache st) mode (src_seg_len + length (ds_tgt st)) (ds_addr_rem st)
             = Some (addr, rest, c') \<and>
           addr < src_seg_len + length (ds_tgt st) \<and>
           length (ds_tgt st) + sz \<le> tgt_len \<and>
           ds_addr_rem st' = rest \<and>
           ds_cache st' = c' \<and>
           ds_tgt st' = copy_loop src_seg (ds_tgt st) addr sz \<and>
           ds_data_rem st' = ds_data_rem st \<and>
           ds_inst_rem st' = ds_inst_rem st"
  using assms
  by (auto simp: exec_half_def Let_def split: if_splits option.splits prod.splits)


(*
  Word-level-guard variants of near_init_preserves_patch_heap /
  same_init_preserves_patch_heap.  The original lemmas use `unat idx < N`
  in the loop guard, but the lifted vcdiff_decode' emits `i < N` at word
  level.  These variants restate the same fact with the word guard so
  that [runs_to_vcg] unification succeeds.
*)
lemma near_init_preserves_patch_heap_word:
  "(whileLoop (\<lambda>idx st. idx < (4 :: 32 word))
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word)
          \<and> heap_bytes t buf n = heap_bytes s0 buf n
          \<and> buf_valid t buf n = buf_valid s0 buf n
	          \<and> heap_w32 t p = heap_w32 s0 p
	          \<and> code_tbl_built_'' t = code_tbl_built_'' s0
	          \<and> code_tbl_'' t = code_tbl_'' s0
	          \<and> heap_typing t = heap_typing s0 \<rbrace>"
proof -
  \<comment> \<open>The word guard `idx < 4` is equivalent to `unat idx < 4` on 32 words
      (since 4 < 2^32), and our existing lemma proves the nat-guard form.\<close>
  have guard_eq: "(\<lambda>idx (st :: lifted_globals). idx < (4 :: 32 word))
                = (\<lambda>idx st. unat idx < 4)"
    by (auto simp: fun_eq_iff word_less_nat_alt unat_numeral)
  show ?thesis
    by (subst guard_eq) (rule near_init_preserves_patch_heap)
qed

lemma same_init_preserves_patch_heap_word:
  "(whileLoop (\<lambda>idx st. idx < (0x300 :: 32 word))
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (0x300 :: 32 word)
          \<and> heap_bytes t buf n = heap_bytes s0 buf n
          \<and> buf_valid t buf n = buf_valid s0 buf n
	          \<and> heap_w32 t p = heap_w32 s0 p
	          \<and> code_tbl_built_'' t = code_tbl_built_'' s0
	          \<and> code_tbl_'' t = code_tbl_'' s0
	          \<and> heap_typing t = heap_typing s0 \<rbrace>"
proof -
  have guard_eq: "(\<lambda>idx (st :: lifted_globals). idx < (0x300 :: 32 word))
                = (\<lambda>idx st. unat idx < 0x300)"
    by (auto simp: fun_eq_iff word_less_nat_alt unat_numeral)
  show ?thesis
    by (subst guard_eq) (rule same_init_preserves_patch_heap)
qed

lemma near_init_preserves_setup_word:
  "(whileLoop (\<lambda>idx st. idx < (4 :: 32 word))
      (\<lambda>idx. do {
          modify (near_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (4 :: 32 word)
          \<and> heap_bytes t patch patch_n = heap_bytes s0 patch patch_n
          \<and> heap_bytes t src src_n = heap_bytes s0 src src_n
          \<and> buf_valid t patch patch_n = buf_valid s0 patch patch_n
          \<and> buf_valid t src src_n = buf_valid s0 src src_n
	          \<and> heap_w32 t out_len = heap_w32 s0 out_len
	          \<and> code_tbl_built_'' t = code_tbl_built_'' s0
	          \<and> code_tbl_'' t = code_tbl_'' s0
	          \<and> heap_typing t = heap_typing s0 \<rbrace>"
  using near_init_preserves_patch_heap_word
          [where buf = patch and n = patch_n and p = out_len]
        near_init_preserves_patch_heap_word
          [where buf = src and n = src_n and p = out_len]
  by (simp add: runs_to_conj)

lemma same_init_preserves_setup_word:
  "(whileLoop (\<lambda>idx st. idx < (0x300 :: 32 word))
      (\<lambda>idx. do {
          modify (same_arr_''_update (\<lambda>a. Arrays.update a (unat idx) 0));
          return (idx + 1)
        }) (0 :: 32 word) :: (32 word, lifted_globals) res_monad) \<bullet> s0
    \<lbrace> \<lambda>r t. r = Result (0x300 :: 32 word)
          \<and> heap_bytes t patch patch_n = heap_bytes s0 patch patch_n
          \<and> heap_bytes t src src_n = heap_bytes s0 src src_n
          \<and> buf_valid t patch patch_n = buf_valid s0 patch patch_n
          \<and> buf_valid t src src_n = buf_valid s0 src src_n
	          \<and> heap_w32 t out_len = heap_w32 s0 out_len
	          \<and> code_tbl_built_'' t = code_tbl_built_'' s0
	          \<and> code_tbl_'' t = code_tbl_'' s0
	          \<and> heap_typing t = heap_typing s0 \<rbrace>"
  using same_init_preserves_patch_heap_word
          [where buf = patch and n = patch_n and p = out_len]
        same_init_preserves_patch_heap_word
          [where buf = src and n = src_n and p = out_len]
  by (simp add: runs_to_conj)


(*
  ----------------------------------------------------------------------
  Outer-loop residual obligations in vcdiff_decode'_spec.

  Each of the 4 top-level branches (code_tbl ∈ {0,1} × has-app-header
  ∈ {0,1}) reaches the same outer whileLoop after its setup prefix.
  Applying `runs_to_weaken[OF outer_whileLoop_correct_abstract]` at
  those 4 sites unifies cleanly and leaves 4 per-branch subgoals:

    (a) inv_entry     — decode_loop_inv_plus at the entry state
                        (data_cursor = data_pos, inst_cursor = inst_pos,
                        addr_cursor = addr_pos, tp = 0, np = 0).
                        Follows from decode_loop_inv_init +
                        decode_loop_inv_plus_entry, using the pure-spec
                        decode_loop_terminates fact.
    (b) body_preserves — one outer-iteration VCG: reads the opcode,
                        dispatches through the nested `which ∈ {0,1}`
                        whileLoop (add/run/copy bodies with inner byte-
                        copy whileLoops), and restores the invariant
                        with strict ic advancement.  Proof uses
                        decode_loop_inv_plus_advance after identifying
                        the abstract decode_one step.
    (c) ie_le         — unat inst_end ≤ patch_n.  Follows from
                        the window prefix's cursor bounds.
    (d) exit_weakening — after the whileLoop post gives
                        ic = inst_end ∧ heap_bytes t' out (unat tp) = tgt
                        ∧ unat tp = tgt_len, the trailing cursor-
                        consistency asserts and out_len write achieve
                        the overall postcondition; identical across all
                        4 branches.

  The four branches share the same body_preserves shape — they differ
  only in which captured values bind to `data_end, inst_end, addr_end,
  src_seg_off, src_seg_len, tgt_len, src_seg, tgt`.  Instantiating each
  against the concrete witness names (e.g. `pos_C vaaaab + ...`) is the
  remaining work.
  ---------------------------------------------------------------------- *)

(*
  Target theorem for the rescue plan (planning/refine-progress.md).

  States full functional correctness of the C decoder against the pure
  decode_spec, over the simplified-VCDIFF input class covered by the
  spec layer.  Currently sorry; Step 1 of the rescue plan anchors the
  postcondition shape for every intermediate lemma.
*)
lemma vcdiff_decode'_spec:
  fixes patch :: "8 word ptr" and patch_len :: "32 word"
    and src   :: "8 word ptr" and src_len   :: "32 word"
    and out   :: "8 word ptr" and out_cap   :: "32 word"
    and out_len :: "32 word ptr"
    and s :: lifted_globals
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch (unat patch_len)"
      and src_ok:   "buf_valid s src   (unat src_len)"
      and src_nonnull: "src \<noteq> NULL"
      and out_ok:   "buf_valid s out   (unat out_cap)"
      and code_tbl_ready: "code_tbl_built_'' s \<noteq> 0"
      and out_patch_disj:
        "\<forall>i < unat out_cap. \<forall>j < unat patch_len.
             out +\<^sub>p int i \<noteq> patch +\<^sub>p int j"
      and out_src_disj:
        "\<forall>i < unat out_cap. \<forall>j < unat src_len.
             out +\<^sub>p int i \<noteq> src +\<^sub>p int j"
      and out_inj:
        "\<forall>i < unat out_cap. \<forall>j < unat out_cap.
             i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j"
      \<comment> \<open>Precondition that the output buffer is large enough for whatever
          target the spec produces.  Without this the theorem's Inl branch
          is false: a spec that produces a large tgt but a small out_cap
          causes C to return OVERRUN, not success.\<close>
      and out_cap_enough:
        "\<And>tgt. decode_spec (heap_bytes s patch (unat patch_len))
                            (heap_bytes s src (unat src_len)) = Inl tgt \<Longrightarrow>
               length tgt \<le> unat out_cap"
      and source_windows_in_bounds:
        "\<And>rest win tail.
           parse_header (heap_bytes s patch (unat patch_len)) = Inl rest \<Longrightarrow>
           parse_window rest = Inl (win, tail) \<Longrightarrow>
           pw_src_seg_off win \<le> unat src_len \<and>
           pw_src_seg_len win \<le> unat src_len - pw_src_seg_off win"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t.
             case decode_spec (heap_bytes s patch (unat patch_len))
                              (heap_bytes s src   (unat src_len)) of
               Inl tgt \<Rightarrow> r = Result (0 :: int) \<and>
                          unat (heap_w32 t out_len) = length tgt \<and>
                          heap_bytes t out (length tgt) = tgt
             | Inr _   \<Rightarrow> (\<exists>e. r = Result (e :: int) \<and> e \<noteq> 0) \<rbrace>"
proof (cases "decode_spec (heap_bytes s patch (unat patch_len))
                           (heap_bytes s src   (unat src_len))")
  case (Inl tgt)
  \<comment> \<open>Soundness: if the spec accepts the input, the C decoder produces
      the same target bytes and returns VCD_OK.

      Two-step strategy: prove (weak) output matches whenever r = Result 0,
      and (strong) r = Result 0 holds.  The weak form's throw-branches
      are vacuous, which avoids the 31-subgoal explosion from the
      conjunctive postcondition.\<close>
  \<comment> \<open>Extract facts from the Inl hypothesis via parse_header.\<close>
  obtain rest where ph: "parse_header (heap_bytes s patch (unat patch_len)) = Inl rest"
    using Inl unfolding decode_spec_def by (auto split: sum.splits)
  from ph obtain b0 b1 b2 b3 hi body where
    bs_form: "heap_bytes s patch (unat patch_len) = b0 # b1 # b2 # b3 # hi # body" and
    magic: "[b0, b1, b2, b3] = [0xD6, 0xC3, 0xC4, 0x00]" and
    hdr3: "hi AND 0x03 = 0"
    unfolding parse_header_def
    by (auto split: list.splits if_splits)
  from magic have b0_eq: "b0 = 0xD6" and b1_eq: "b1 = 0xC3"
    and b2_eq: "b2 = 0xC4" and b3_eq: "b3 = 0x00" by auto
  have len_ge5: "unat patch_len \<ge> 5"
  proof -
    have "length (heap_bytes s patch (unat patch_len)) \<ge> 5"
      using bs_form by simp
    thus ?thesis by simp
  qed
  have len_ge5_word: "(5 :: 32 word) \<le> patch_len"
    using len_ge5 by (simp add: word_le_nat_alt)
  have patch_n_ok: "buf_valid s patch (unat patch_len)" using patch_ok .
  have patchi_ok:
    "\<And>i. i < 5 \<Longrightarrow> ptr_valid (heap_typing s) (patch +\<^sub>p int i)"
    using buf_validD[OF patch_ok] len_ge5 by simp
  have nth_eq: "\<And>i. i < 5 \<Longrightarrow>
      heap_w8 s (patch +\<^sub>p int i) = heap_bytes s patch (unat patch_len) ! i"
    using len_ge5 by (simp add: heap_bytes_nth)
  have magic0_v: "heap_w8 s patch = 0xD6"
    using nth_eq[of 0] bs_form b0_eq by simp
  have magic1_v: "heap_w8 s (patch +\<^sub>p 1) = 0xC3"
    using nth_eq[of 1] bs_form b1_eq by simp
  have magic2_v: "heap_w8 s (patch +\<^sub>p 2) = 0xC4"
    using nth_eq[of 2] bs_form b2_eq by simp
  have magic3_v: "heap_w8 s (patch +\<^sub>p 3) = 0"
    using nth_eq[of 3] bs_form b3_eq by simp
  have hi_v: "heap_w8 s (patch +\<^sub>p 4) = hi"
    using nth_eq[of 4] bs_form by simp
  have body_from_drop5:
    "body = drop 5 (heap_bytes s patch (unat patch_len))"
    using bs_form by simp
  define app_bit where "app_bit = (hi AND 0x04 \<noteq> 0)"
  have parse_header_app:
    "app_bit \<Longrightarrow> \<exists>app_len rest'.
        varint_decode body = Some (app_len, rest') \<and>
        app_len \<le> length rest' \<and>
        rest = drop app_len rest'"
    using ph bs_form hdr3 unfolding parse_header_def app_bit_def
    by (auto split: list.splits if_splits option.splits)
  have parse_header_noapp:
    "\<not> app_bit \<Longrightarrow> rest = body"
    using ph bs_form hdr3 unfolding parse_header_def app_bit_def
    by (auto split: list.splits if_splits option.splits)
  have ucast_and_4_equiv:
    "(UCAST(8 \<rightarrow> 32) hi AND 4 \<noteq> 0) = (hi AND 4 \<noteq> 0)"
    by word_bitwise
  \<comment> \<open>Window-parse facts from Inl.\<close>
  obtain win tail where
    pw: "parse_window rest = Inl (win, tail)"
    using Inl ph unfolding decode_spec_def
    by (auto split: sum.splits)
	  have aw: "apply_window win (heap_bytes s src (unat src_len)) = Inl tgt"
	    using apply_window_from_decode_spec[OF Inl ph pw] .
	  have win_src_bounds:
	    "pw_src_seg_off win \<le> unat src_len \<and>
	     pw_src_seg_len win \<le> unat src_len - pw_src_seg_off win"
	    using source_windows_in_bounds[OF ph pw] .
  \<comment> \<open>Extract the decode_loop-termination fact for the pure spec.\<close>
  define initial_dst where
    "initial_dst = \<lparr> ds_data_rem = pw_data win,
                     ds_inst_rem = pw_inst win,
                     ds_addr_rem = pw_addr win,
                     ds_cache = cache_init,
                     ds_tgt = [] \<rparr>"
  define pw_src_seg where
    "pw_src_seg =
      (if pw_src_seg_len win = 0 then []
       else take (pw_src_seg_len win)
              (drop (pw_src_seg_off win) (heap_bytes s src (unat src_len))))"
	  have decode_loop_terminates:
	    "\<exists>dst_final. decode_loop (length (ds_inst_rem initial_dst)) pw_src_seg
	                   (pw_src_seg_len win) (pw_tgt_len win) initial_dst = Inl dst_final \<and>
	                 length (ds_tgt dst_final) = pw_tgt_len win \<and>
	                 ds_tgt dst_final = tgt \<and>
	                 ds_data_rem dst_final = [] \<and>
	                 ds_addr_rem dst_final = []"
	    using decode_loop_from_apply_window[OF aw, of pw_src_seg]
	    unfolding initial_dst_def pw_src_seg_def by auto
	  have tgt_len_eq: "length tgt = pw_tgt_len win"
	    using decode_loop_terminates by auto
	  have app_source_prefix_decodes:
	    "\<And>(td :: lifted_globals) (va :: pr_t_C).
	      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
	      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)) \<Longrightarrow>
	      pr_t_C.err_C va = 0 \<Longrightarrow>
	      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
	      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
	      heap_bytes td patch (unat patch_len) =
	        heap_bytes s patch (unat patch_len) \<Longrightarrow>
	      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
	      UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1 \<Longrightarrow>
	      \<exists>rest1 rest2 rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
		        varint_decode
		          (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		            (heap_bytes td patch (unat patch_len))) =
		          Some (pw_src_seg_len win, rest1) \<and>
		        varint_decode rest1 = Some (pw_src_seg_off win, rest2) \<and>
		        varint_decode rest2 = Some (dlen, rest3) \<and>
		        varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
		        pop_byte rest4 = Some (0, rest5) \<and>
		        varint_decode rest5 = Some (data_len, rest6) \<and>
		        varint_decode rest6 = Some (inst_len, rest7) \<and>
		        varint_decode rest7 = Some (addr_len, rest8) \<and>
		        alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
		        dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len \<and>
		        alen =
		          (if UCAST(8 \<rightarrow> 32)
		                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		              (4 :: 32 word) \<noteq> 0
		           then 4 else 0)"
	  proof -
	    fix td :: lifted_globals and va :: pr_t_C
	    assume hi4_c:
	      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
	    assume app_read:
	      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)"
	    assume app_ok: "pr_t_C.err_C va = 0"
	    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
	    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
	    assume heap_eq: "heap_bytes td patch (unat patch_len) =
	                     heap_bytes s patch (unat patch_len)"
	    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
	    assume source_set:
	      "UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1"
	    let ?bs = "heap_bytes s patch (unat patch_len)"
	    let ?k_w = "pr_t_C.pos_C va + val_C va"
	    let ?k = "unat ?k_w"
	    have hi4: "hi AND 4 \<noteq> 0"
	      using hi4_c hi_v ucast_and_4_equiv by simp
	    obtain app_len app_rest where
	      vd: "varint_decode body = Some (app_len, app_rest)"
	      and rest_eq: "rest = drop app_len app_rest"
	      using parse_header_app[unfolded app_bit_def] hi4 by blast
	    have vd_bs: "varint_decode (drop 5 ?bs) = Some (app_len, app_rest)"
	      using vd body_from_drop5 by simp
	    have app_len_eq: "app_len = unat (val_C va)"
	      and pos_eq: "unat (pr_t_C.pos_C va) = unat patch_len - length app_rest"
	      using app_read app_ok vd_bs by auto
	    have pos_drop: "drop (unat (pr_t_C.pos_C va)) ?bs = app_rest"
	      using varint_decode_drop_rest[OF vd_bs] pos_eq by simp
	    have val_le: "val_C va \<le> patch_len - pr_t_C.pos_C va"
	      using app_len_ok by (simp add: word_le_not_less)
	    have k_unat: "?k = unat (pr_t_C.pos_C va) + unat (val_C va)"
	      using val_le pos_le
	      apply (simp add: word_le_nat_alt unat_sub)
	      apply (subst unat_word_ariths(1))
	      using unat_lt2p[of patch_len]
	      apply auto
	      done
	    have rest_at_k: "drop ?k ?bs = rest"
	    proof -
	      have "drop ?k ?bs =
	            drop (unat (val_C va))
	              (drop (unat (pr_t_C.pos_C va)) ?bs)"
	        using k_unat by (simp add: drop_drop add.commute)
	      also have "\<dots> = drop (unat (val_C va)) app_rest"
	        using pos_drop by simp
	      also have "\<dots> = rest"
	        using rest_eq app_len_eq by simp
	      finally show ?thesis .
	    qed
	    have parsed_at_k: "parse_window (drop ?k ?bs) = Inl (win, tail)"
	      using pw rest_at_k by simp
	    have k_lt: "?k < length ?bs"
	      using k_lt_w by (simp add: word_less_nat_alt)
	    have nth_s: "?bs ! ?k = heap_w8 s (patch +\<^sub>p uint ?k_w)"
	      using k_lt by (simp add: heap_bytes_nth)
	    have heap_w8_eq:
	      "heap_w8 td (patch +\<^sub>p uint ?k_w) =
	       heap_w8 s (patch +\<^sub>p uint ?k_w)"
	      using heap_eq k_lt by (auto dest: heap_bytes_eq_heap_w8_uintD)
	    have nth_eq: "?bs ! ?k = heap_w8 td (patch +\<^sub>p uint ?k_w)"
	      using nth_s heap_w8_eq by simp
		    have source_set8: "(?bs ! ?k) AND (1 :: 8 word) \<noteq> 0"
		    proof -
		      have "heap_w8 td (patch +\<^sub>p uint ?k_w) AND (1 :: 8 word) \<noteq> 0"
		        using source_set by word_bitwise
		      thus ?thesis using nth_eq by simp
		    qed
		    have adler_len_eq:
		      "(if (?bs ! ?k) AND (0x04 :: 8 word) \<noteq> 0 then 4 else 0) =
		       (if UCAST(8 \<rightarrow> 32)
		             (heap_w8 td (patch +\<^sub>p uint ?k_w)) AND (4 :: 32 word) \<noteq> 0
		        then 4 else 0)"
		    proof -
		      have ucast4:
		        "(UCAST(8 \<rightarrow> 32)
		          (heap_w8 td (patch +\<^sub>p uint ?k_w)) AND (4 :: 32 word) \<noteq> 0) =
		         (heap_w8 td (patch +\<^sub>p uint ?k_w) AND (0x04 :: 8 word) \<noteq> 0)"
		        by word_bitwise
		      show ?thesis using nth_eq ucast4 by simp
		    qed
		    obtain rest1 rest2 rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len where
	      dec1: "varint_decode (drop (Suc ?k) ?bs) =
	               Some (pw_src_seg_len win, rest1)"
	      and dec2: "varint_decode rest1 = Some (pw_src_seg_off win, rest2)"
	      and dec3: "varint_decode rest2 = Some (dlen, rest3)"
	      and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
	      and di0: "pop_byte rest4 = Some (0, rest5)"
	      and dec5: "varint_decode rest5 = Some (data_len, rest6)"
	      and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
	      and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
	      and sizes_ok:
	        "(if (?bs ! ?k) AND (0x04 :: 8 word) \<noteq> 0 then 4 else 0) +
	           data_len + inst_len + addr_len \<le> length rest8"
	      and dlen_exact:
	        "dlen = (length rest3 - length rest8) +
	                (if (?bs ! ?k) AND (0x04 :: 8 word) \<noteq> 0 then 4 else 0) +
	                data_len + inst_len + addr_len"
	      using parse_window_source_full_decodes[OF parsed_at_k k_lt source_set8]
	      by blast
	    have k1_unat: "unat (?k_w + 1) = Suc ?k"
	    proof -
	      have "?k_w < patch_len" using k_lt_w .
	      hence "unat (?k_w + 1) = unat ?k_w + 1"
	        by (rule unat_x_plus_1)
	      thus ?thesis by simp
	    qed
	    have dec1_td:
	      "varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) =
	       Some (pw_src_seg_len win, rest1)"
	      using dec1 k1_unat heap_eq by simp
	    show "\<exists>rest1 rest2 rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	            (heap_bytes td patch (unat patch_len))) =
	          Some (pw_src_seg_len win, rest1) \<and>
	        varint_decode rest1 = Some (pw_src_seg_off win, rest2) \<and>
	        varint_decode rest2 = Some (dlen, rest3) \<and>
	        varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
	        pop_byte rest4 = Some (0, rest5) \<and>
	        varint_decode rest5 = Some (data_len, rest6) \<and>
	        varint_decode rest6 = Some (inst_len, rest7) \<and>
		        varint_decode rest7 = Some (addr_len, rest8) \<and>
		        alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
		        dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len \<and>
		        alen =
		          (if UCAST(8 \<rightarrow> 32)
		                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		              (4 :: 32 word) \<noteq> 0
		           then 4 else 0)"
		      using dec1_td dec2 dec3 dec4 di0 dec5 dec6 dec7 sizes_ok dlen_exact
		            adler_len_eq by blast
	  qed
	  have app_source_len_decode_some:
	    "\<And>(td :: lifted_globals) (va :: pr_t_C).
	      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
	      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)) \<Longrightarrow>
	      pr_t_C.err_C va = 0 \<Longrightarrow>
	      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
	      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
	      heap_bytes td patch (unat patch_len) =
	        heap_bytes s patch (unat patch_len) \<Longrightarrow>
	      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
	      UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1 \<Longrightarrow>
	      \<exists>nv rest.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	    using app_source_prefix_decodes by blast
	  have app_source_off_decode_some:
	    "\<And>(td :: lifted_globals) (va :: pr_t_C) (vaa :: pr_t_C).
	      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
	      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)) \<Longrightarrow>
	      pr_t_C.err_C va = 0 \<Longrightarrow>
	      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
	      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
	      heap_bytes td patch (unat patch_len) =
	        heap_bytes s patch (unat patch_len) \<Longrightarrow>
	      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
	      UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)) \<Longrightarrow>
	      pr_t_C.err_C vaa = 0 \<Longrightarrow>
	      \<exists>nv rest.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C vaa))
	            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	  proof -
	    fix td :: lifted_globals and va vaa :: pr_t_C
	    assume hi4_c:
	      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
	    assume app_read:
	      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)"
	    assume app_ok: "pr_t_C.err_C va = 0"
	    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
	    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
	    assume heap_eq: "heap_bytes td patch (unat patch_len) =
	                     heap_bytes s patch (unat patch_len)"
	    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
	    assume source_set:
	      "UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1"
	    assume src_len_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)"
	    assume src_len_ok: "pr_t_C.err_C vaa = 0"
	    obtain rest1 rest2 rest3 dlen where
	      dec1: "varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) =
	        Some (pw_src_seg_len win, rest1)"
	      and dec2: "varint_decode rest1 = Some (pw_src_seg_off win, rest2)"
	      using app_source_prefix_decodes[OF hi4_c app_read app_ok pos_le app_len_ok
	        heap_eq k_lt_w source_set]
	      by blast
	    have pos_vaa:
	      "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest1"
	      using src_len_read src_len_ok dec1 by simp
	    have drop_rest1:
	      "drop (unat (pr_t_C.pos_C vaa))
	        (heap_bytes td patch (unat patch_len)) = rest1"
	      using varint_decode_drop_rest[OF dec1] pos_vaa by simp
	    show "\<exists>nv rest.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C vaa))
	            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	      using dec2 drop_rest1 by simp
	  qed
	  have app_source_values:
	    "\<And>(td :: lifted_globals) (va :: pr_t_C) (vaa :: pr_t_C) (vaaa :: pr_t_C).
	      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
	      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)) \<Longrightarrow>
	      pr_t_C.err_C va = 0 \<Longrightarrow>
	      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
	      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
	      heap_bytes td patch (unat patch_len) =
	        heap_bytes s patch (unat patch_len) \<Longrightarrow>
	      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
	      UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)) \<Longrightarrow>
	      pr_t_C.err_C vaa = 0 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)) \<Longrightarrow>
	      pr_t_C.err_C vaaa = 0 \<Longrightarrow>
	      unat (val_C vaa) = pw_src_seg_len win \<and>
	      unat (val_C vaaa) = pw_src_seg_off win"
	  proof -
	    fix td :: lifted_globals and va vaa vaaa :: pr_t_C
	    assume hi4_c:
	      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
	    assume app_read:
	      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)"
	    assume app_ok: "pr_t_C.err_C va = 0"
	    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
	    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
	    assume heap_eq: "heap_bytes td patch (unat patch_len) =
	                     heap_bytes s patch (unat patch_len)"
	    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
	    assume source_set:
	      "UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1"
	    assume src_len_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)"
	    assume src_len_ok: "pr_t_C.err_C vaa = 0"
	    assume src_off_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)"
	    assume src_off_ok: "pr_t_C.err_C vaaa = 0"
	    obtain rest1 rest2 rest3 dlen where
	      dec1: "varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) =
	        Some (pw_src_seg_len win, rest1)"
	      and dec2: "varint_decode rest1 = Some (pw_src_seg_off win, rest2)"
	      using app_source_prefix_decodes[OF hi4_c app_read app_ok pos_le app_len_ok
	        heap_eq k_lt_w source_set]
	      by blast
	    have len_val: "unat (val_C vaa) = pw_src_seg_len win"
	      using src_len_read src_len_ok dec1 by simp
	    have pos_vaa:
	      "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest1"
	      using src_len_read src_len_ok dec1 by simp
	    have drop_rest1:
	      "drop (unat (pr_t_C.pos_C vaa))
	        (heap_bytes td patch (unat patch_len)) = rest1"
	      using varint_decode_drop_rest[OF dec1] pos_vaa by simp
	    have dec2_td:
	      "varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) =
	       Some (pw_src_seg_off win, rest2)"
	      using dec2 drop_rest1 by simp
	    have off_val: "unat (val_C vaaa) = pw_src_seg_off win"
	      using src_off_read src_off_ok dec2_td by simp
	    show "unat (val_C vaa) = pw_src_seg_len win \<and>
	          unat (val_C vaaa) = pw_src_seg_off win"
	      using len_val off_val by simp
	  qed
	  have app_source_dlen_decode_some:
	    "\<And>(td :: lifted_globals) (va :: pr_t_C) (vaa :: pr_t_C) (vaaa :: pr_t_C).
	      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
	      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)) \<Longrightarrow>
	      pr_t_C.err_C va = 0 \<Longrightarrow>
	      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
	      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
	      heap_bytes td patch (unat patch_len) =
	        heap_bytes s patch (unat patch_len) \<Longrightarrow>
	      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
	      UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)) \<Longrightarrow>
	      pr_t_C.err_C vaa = 0 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)) \<Longrightarrow>
	      pr_t_C.err_C vaaa = 0 \<Longrightarrow>
	      \<exists>nv rest.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C vaaa))
	            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	  proof -
	    fix td :: lifted_globals and va vaa vaaa :: pr_t_C
	    assume hi4_c:
	      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
	    assume app_read:
	      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)"
	    assume app_ok: "pr_t_C.err_C va = 0"
	    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
	    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
	    assume heap_eq: "heap_bytes td patch (unat patch_len) =
	                     heap_bytes s patch (unat patch_len)"
	    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
	    assume source_set:
	      "UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1"
	    assume src_len_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)"
	    assume src_len_ok: "pr_t_C.err_C vaa = 0"
	    assume src_off_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)"
	    assume src_off_ok: "pr_t_C.err_C vaaa = 0"
	    obtain rest1 rest2 rest3 dlen where
	      dec1: "varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) =
	        Some (pw_src_seg_len win, rest1)"
	      and dec2: "varint_decode rest1 = Some (pw_src_seg_off win, rest2)"
	      and dec3: "varint_decode rest2 = Some (dlen, rest3)"
	      using app_source_prefix_decodes[OF hi4_c app_read app_ok pos_le app_len_ok
	        heap_eq k_lt_w source_set]
	      by blast
	    have pos_vaa:
	      "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest1"
	      using src_len_read src_len_ok dec1 by simp
	    have drop_rest1:
	      "drop (unat (pr_t_C.pos_C vaa))
	        (heap_bytes td patch (unat patch_len)) = rest1"
	      using varint_decode_drop_rest[OF dec1] pos_vaa by simp
	    have dec2_td:
	      "varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) =
	       Some (pw_src_seg_off win, rest2)"
	      using dec2 drop_rest1 by simp
	    have pos_vaaa:
	      "unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest2"
	      using src_off_read src_off_ok dec2_td by simp
	    have drop_rest2:
	      "drop (unat (pr_t_C.pos_C vaaa))
	        (heap_bytes td patch (unat patch_len)) = rest2"
	      using varint_decode_drop_rest[OF dec2_td] pos_vaaa by simp
	    show "\<exists>nv rest.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C vaaa))
	            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	      using dec3 drop_rest2 by simp
	  qed
	  have app_source_dlen_stage:
	    "\<And>(td :: lifted_globals) (va :: pr_t_C) (vaa :: pr_t_C) (vaaa :: pr_t_C).
	      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
	      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)) \<Longrightarrow>
	      pr_t_C.err_C va = 0 \<Longrightarrow>
	      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
	      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
	      heap_bytes td patch (unat patch_len) =
	        heap_bytes s patch (unat patch_len) \<Longrightarrow>
	      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
	      UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)) \<Longrightarrow>
	      pr_t_C.err_C vaa = 0 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)) \<Longrightarrow>
	      pr_t_C.err_C vaaa = 0 \<Longrightarrow>
	      \<exists>rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C vaaa))
	            (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3) \<and>
	        varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
		        pop_byte rest4 = Some (0, rest5) \<and>
		        varint_decode rest5 = Some (data_len, rest6) \<and>
		        varint_decode rest6 = Some (inst_len, rest7) \<and>
		        varint_decode rest7 = Some (addr_len, rest8) \<and>
		        alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
		        dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len \<and>
		        alen =
		          (if UCAST(8 \<rightarrow> 32)
		                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		              (4 :: 32 word) \<noteq> 0
		           then 4 else 0)"
	  proof -
	    fix td :: lifted_globals and va vaa vaaa :: pr_t_C
	    assume hi4_c:
	      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
	    assume app_read:
	      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)"
	    assume app_ok: "pr_t_C.err_C va = 0"
	    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
	    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
	    assume heap_eq: "heap_bytes td patch (unat patch_len) =
	                     heap_bytes s patch (unat patch_len)"
	    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
	    assume source_set:
	      "UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1"
	    assume src_len_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)"
	    assume src_len_ok: "pr_t_C.err_C vaa = 0"
	    assume src_off_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)"
	    assume src_off_ok: "pr_t_C.err_C vaaa = 0"
	    obtain rest1 rest2 rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
	      dec1: "varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) =
	        Some (pw_src_seg_len win, rest1)"
	      and dec2: "varint_decode rest1 = Some (pw_src_seg_off win, rest2)"
	      and dec3: "varint_decode rest2 = Some (dlen, rest3)"
	      and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
	      and di0: "pop_byte rest4 = Some (0, rest5)"
	      and dec5: "varint_decode rest5 = Some (data_len, rest6)"
	      and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
		      and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
		      and sizes_ok: "alen + data_len + inst_len + addr_len \<le> length rest8"
		      and dlen_exact: "dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len"
		      and adler_len_eq:
		        "alen =
		          (if UCAST(8 \<rightarrow> 32)
		                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		              (4 :: 32 word) \<noteq> 0
		           then 4 else 0)"
		      using app_source_prefix_decodes[OF hi4_c app_read app_ok pos_le app_len_ok
		        heap_eq k_lt_w source_set]
		      by blast
	    have pos_vaa:
	      "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest1"
	      using src_len_read src_len_ok dec1 by simp
	    have drop_rest1:
	      "drop (unat (pr_t_C.pos_C vaa))
	        (heap_bytes td patch (unat patch_len)) = rest1"
	      using varint_decode_drop_rest[OF dec1] pos_vaa by simp
	    have dec2_td:
	      "varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) =
	       Some (pw_src_seg_off win, rest2)"
	      using dec2 drop_rest1 by simp
	    have pos_vaaa:
	      "unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest2"
	      using src_off_read src_off_ok dec2_td by simp
	    have drop_rest2:
	      "drop (unat (pr_t_C.pos_C vaaa))
	        (heap_bytes td patch (unat patch_len)) = rest2"
	      using varint_decode_drop_rest[OF dec2_td] pos_vaaa by simp
	    have dec3_td:
	      "varint_decode
	        (drop (unat (pr_t_C.pos_C vaaa))
	          (heap_bytes td patch (unat patch_len))) =
	       Some (dlen, rest3)"
	      using dec3 drop_rest2 by simp
	    show "\<exists>rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C vaaa))
	            (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3) \<and>
	        varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
	        pop_byte rest4 = Some (0, rest5) \<and>
		        varint_decode rest5 = Some (data_len, rest6) \<and>
		        varint_decode rest6 = Some (inst_len, rest7) \<and>
		        varint_decode rest7 = Some (addr_len, rest8) \<and>
		        alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
		        dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len \<and>
		        alen =
		          (if UCAST(8 \<rightarrow> 32)
		                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		              (4 :: 32 word) \<noteq> 0
		           then 4 else 0)"
		      using dec3_td dec4 di0 dec5 dec6 dec7 sizes_ok dlen_exact
		            adler_len_eq by blast
	  qed
	  have app_source_tgt_decode_some:
	    "\<And>(td :: lifted_globals) (va :: pr_t_C) (vaa :: pr_t_C)
	        (vaaa :: pr_t_C) (vaaaa :: pr_t_C).
	      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
	      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)) \<Longrightarrow>
	      pr_t_C.err_C va = 0 \<Longrightarrow>
	      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
	      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
	      heap_bytes td patch (unat patch_len) =
	        heap_bytes s patch (unat patch_len) \<Longrightarrow>
	      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
	      UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)) \<Longrightarrow>
	      pr_t_C.err_C vaa = 0 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)) \<Longrightarrow>
	      pr_t_C.err_C vaaa = 0 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C vaaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaaa)) \<Longrightarrow>
	      pr_t_C.err_C vaaaa = 0 \<Longrightarrow>
	      \<exists>nv rest.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C vaaaa))
	            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	  proof -
	    fix td :: lifted_globals and va vaa vaaa vaaaa :: pr_t_C
	    assume hi4_c:
	      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
	    assume app_read:
	      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)"
	    assume app_ok: "pr_t_C.err_C va = 0"
	    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
	    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
	    assume heap_eq: "heap_bytes td patch (unat patch_len) =
	                     heap_bytes s patch (unat patch_len)"
	    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
	    assume source_set:
	      "UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1"
	    assume src_len_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)"
	    assume src_len_ok: "pr_t_C.err_C vaa = 0"
	    assume src_off_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)"
	    assume src_off_ok: "pr_t_C.err_C vaaa = 0"
	    assume dlen_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C vaaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaaa)"
	    assume dlen_ok: "pr_t_C.err_C vaaaa = 0"
	    obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
	      dec3: "varint_decode
	        (drop (unat (pr_t_C.pos_C vaaa))
	          (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3)"
	      and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
	      using app_source_dlen_stage[OF hi4_c app_read app_ok pos_le app_len_ok heap_eq
	        k_lt_w source_set src_len_read src_len_ok src_off_read src_off_ok]
	      by blast
	    have pos_vaaaa:
	      "unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest3"
	      using dlen_read dlen_ok dec3 by simp
	    have drop_rest3:
	      "drop (unat (pr_t_C.pos_C vaaaa))
	        (heap_bytes td patch (unat patch_len)) = rest3"
	      using varint_decode_drop_rest[OF dec3] pos_vaaaa by simp
	    show "\<exists>nv rest.
	        varint_decode
	          (drop (unat (pr_t_C.pos_C vaaaa))
	            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	      using dec4 drop_rest3 by simp
	  qed
	  have app_source_tgt_value:
	    "\<And>(td :: lifted_globals) (va :: pr_t_C) (vaa :: pr_t_C)
	        (vaaa :: pr_t_C) (vaaaa :: pr_t_C) (vaaaaa :: pr_t_C).
	      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
	      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)) \<Longrightarrow>
	      pr_t_C.err_C va = 0 \<Longrightarrow>
	      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
	      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
	      heap_bytes td patch (unat patch_len) =
	        heap_bytes s patch (unat patch_len) \<Longrightarrow>
	      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
	      UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)) \<Longrightarrow>
	      pr_t_C.err_C vaa = 0 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)) \<Longrightarrow>
	      pr_t_C.err_C vaaa = 0 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C vaaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaaa)) \<Longrightarrow>
	      pr_t_C.err_C vaaaa = 0 \<Longrightarrow>
	      (case varint_decode
	        (drop (unat (pr_t_C.pos_C vaaaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaaaa)) \<Longrightarrow>
	      pr_t_C.err_C vaaaaa = 0 \<Longrightarrow>
	      unat (val_C vaaaaa) = pw_tgt_len win"
	  proof -
	    fix td :: lifted_globals and va vaa vaaa vaaaa vaaaaa :: pr_t_C
	    assume hi4_c:
	      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
	    assume app_read:
	      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C va = 0 \<and>
	           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
	           nv = unat (val_C va)"
	    assume app_ok: "pr_t_C.err_C va = 0"
	    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
	    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
	    assume heap_eq: "heap_bytes td patch (unat patch_len) =
	                     heap_bytes s patch (unat patch_len)"
	    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
	    assume source_set:
	      "UCAST(8 \<rightarrow> 32)
	        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
	      (1 :: 32 word) = 1"
	    assume src_len_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaa = 0 \<and>
	           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaa)"
	    assume src_len_ok: "pr_t_C.err_C vaa = 0"
	    assume src_off_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C vaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaa)"
	    assume src_off_ok: "pr_t_C.err_C vaaa = 0"
	    assume dlen_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C vaaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaaa)"
	    assume dlen_ok: "pr_t_C.err_C vaaaa = 0"
	    assume tgt_read:
	      "case varint_decode
	        (drop (unat (pr_t_C.pos_C vaaaa))
	          (heap_bytes td patch (unat patch_len))) of
	         None \<Rightarrow> pr_t_C.err_C vaaaaa \<noteq> 0
	       | Some (nv, rest) \<Rightarrow>
	           pr_t_C.err_C vaaaaa = 0 \<and>
	           unat (pr_t_C.pos_C vaaaaa) = unat patch_len - length rest \<and>
	           nv = unat (val_C vaaaaa)"
	    assume tgt_ok: "pr_t_C.err_C vaaaaa = 0"
	    obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
	      dec3: "varint_decode
	        (drop (unat (pr_t_C.pos_C vaaa))
	          (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3)"
	      and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
	      using app_source_dlen_stage[OF hi4_c app_read app_ok pos_le app_len_ok heap_eq
	        k_lt_w source_set src_len_read src_len_ok src_off_read src_off_ok]
	      by blast
	    have pos_vaaaa:
	      "unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest3"
	      using dlen_read dlen_ok dec3 by simp
	    have drop_rest3:
	      "drop (unat (pr_t_C.pos_C vaaaa))
	        (heap_bytes td patch (unat patch_len)) = rest3"
	      using varint_decode_drop_rest[OF dec3] pos_vaaaa by simp
	    have dec4_td:
	      "varint_decode
	        (drop (unat (pr_t_C.pos_C vaaaa))
	          (heap_bytes td patch (unat patch_len))) =
	       Some (pw_tgt_len win, rest4)"
	      using dec4 drop_rest3 by simp
		    show "unat (val_C vaaaaa) = pw_tgt_len win"
		      using tgt_read tgt_ok dec4_td by simp
		  qed
		  have app_source_payload_stage:
		    "\<And>(td :: lifted_globals) (va :: pr_t_C) (vaa :: pr_t_C)
		        (vaaa :: pr_t_C) (vaaaa :: pr_t_C) (vaaaaa :: pr_t_C).
		      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
		      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C va = 0 \<and>
		           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
		           nv = unat (val_C va)) \<Longrightarrow>
		      pr_t_C.err_C va = 0 \<Longrightarrow>
		      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
		      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
		      heap_bytes td patch (unat patch_len) =
		        heap_bytes s patch (unat patch_len) \<Longrightarrow>
		      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
		      UCAST(8 \<rightarrow> 32)
		        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		      (1 :: 32 word) = 1 \<Longrightarrow>
		      (case varint_decode
		        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaa = 0 \<and>
		           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaa)) \<Longrightarrow>
		      pr_t_C.err_C vaa = 0 \<Longrightarrow>
		      (case varint_decode
		        (drop (unat (pr_t_C.pos_C vaa))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaaa = 0 \<and>
		           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaaa)) \<Longrightarrow>
		      pr_t_C.err_C vaaa = 0 \<Longrightarrow>
		      (case varint_decode
		        (drop (unat (pr_t_C.pos_C vaaa))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaaaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaaaa = 0 \<and>
		           unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaaaa)) \<Longrightarrow>
		      pr_t_C.err_C vaaaa = 0 \<Longrightarrow>
		      (case varint_decode
		        (drop (unat (pr_t_C.pos_C vaaaa))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaaaaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaaaaa = 0 \<and>
		           unat (pr_t_C.pos_C vaaaaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaaaaa)) \<Longrightarrow>
		      pr_t_C.err_C vaaaaa = 0 \<Longrightarrow>
		      \<exists>rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
		        varint_decode
		          (drop (unat (pr_t_C.pos_C vaaa))
		            (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3) \<and>
		        drop (unat (pr_t_C.pos_C vaaaa))
		          (heap_bytes td patch (unat patch_len)) = rest3 \<and>
		        varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
		        drop (unat (pr_t_C.pos_C vaaaaa))
		          (heap_bytes td patch (unat patch_len)) = rest4 \<and>
		        pop_byte rest4 = Some (0, rest5) \<and>
		        varint_decode rest5 = Some (data_len, rest6) \<and>
		        varint_decode rest6 = Some (inst_len, rest7) \<and>
			        varint_decode rest7 = Some (addr_len, rest8) \<and>
			        alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
			        dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len \<and>
			        unat (val_C vaaaa) = dlen \<and>
			        unat (val_C vaaaaa) = pw_tgt_len win \<and>
			        alen =
			          (if UCAST(8 \<rightarrow> 32)
			                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			              (4 :: 32 word) \<noteq> 0
			           then 4 else 0)"
		  proof -
		    fix td :: lifted_globals and va vaa vaaa vaaaa vaaaaa :: pr_t_C
		    assume hi4_c:
		      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
		    assume app_read:
		      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C va = 0 \<and>
		           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
		           nv = unat (val_C va)"
		    assume app_ok: "pr_t_C.err_C va = 0"
		    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
		    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
		    assume heap_eq: "heap_bytes td patch (unat patch_len) =
		                     heap_bytes s patch (unat patch_len)"
		    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
		    assume source_set:
		      "UCAST(8 \<rightarrow> 32)
		        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		      (1 :: 32 word) = 1"
		    assume src_len_read:
		      "case varint_decode
		        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaa = 0 \<and>
		           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaa)"
		    assume src_len_ok: "pr_t_C.err_C vaa = 0"
		    assume src_off_read:
		      "case varint_decode
		        (drop (unat (pr_t_C.pos_C vaa))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaaa = 0 \<and>
		           unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaaa)"
		    assume src_off_ok: "pr_t_C.err_C vaaa = 0"
		    assume dlen_read:
		      "case varint_decode
		        (drop (unat (pr_t_C.pos_C vaaa))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaaaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaaaa = 0 \<and>
		           unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaaaa)"
		    assume dlen_ok: "pr_t_C.err_C vaaaa = 0"
		    assume tgt_read:
		      "case varint_decode
		        (drop (unat (pr_t_C.pos_C vaaaa))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaaaaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaaaaa = 0 \<and>
		           unat (pr_t_C.pos_C vaaaaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaaaaa)"
		    assume tgt_ok: "pr_t_C.err_C vaaaaa = 0"
		    obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
		      dec3: "varint_decode
		        (drop (unat (pr_t_C.pos_C vaaa))
		          (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3)"
		      and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
		      and di0: "pop_byte rest4 = Some (0, rest5)"
		      and dec5: "varint_decode rest5 = Some (data_len, rest6)"
		      and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
			      and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
			      and sizes_ok: "alen + data_len + inst_len + addr_len \<le> length rest8"
			      and dlen_exact: "dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len"
			      and adler_len_eq:
			        "alen =
			          (if UCAST(8 \<rightarrow> 32)
			                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			              (4 :: 32 word) \<noteq> 0
			           then 4 else 0)"
			      using app_source_dlen_stage[OF hi4_c app_read app_ok pos_le app_len_ok heap_eq
			        k_lt_w source_set src_len_read src_len_ok src_off_read src_off_ok]
			      by blast
		    have pos_vaaaa:
		      "unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest3"
		      using dlen_read dlen_ok dec3 by simp
		    have drop_rest3:
		      "drop (unat (pr_t_C.pos_C vaaaa))
		        (heap_bytes td patch (unat patch_len)) = rest3"
		      using varint_decode_drop_rest[OF dec3] pos_vaaaa by simp
		    have dec4_td:
		      "varint_decode
		        (drop (unat (pr_t_C.pos_C vaaaa))
		          (heap_bytes td patch (unat patch_len))) =
		       Some (pw_tgt_len win, rest4)"
		      using dec4 drop_rest3 by simp
		    have pos_vaaaaa:
		      "unat (pr_t_C.pos_C vaaaaa) = unat patch_len - length rest4"
		      using tgt_read tgt_ok dec4_td by simp
		    have drop_rest4:
		      "drop (unat (pr_t_C.pos_C vaaaaa))
		        (heap_bytes td patch (unat patch_len)) = rest4"
		      using varint_decode_drop_rest[OF dec4_td] pos_vaaaaa by simp
		    have dlen_val: "unat (val_C vaaaa) = dlen"
		      using dlen_read dlen_ok dec3 by simp
		    have tgt_val: "unat (val_C vaaaaa) = pw_tgt_len win"
		      using tgt_read tgt_ok dec4_td by simp
		    show "\<exists>rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
		        varint_decode
		          (drop (unat (pr_t_C.pos_C vaaa))
		            (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3) \<and>
		        drop (unat (pr_t_C.pos_C vaaaa))
		          (heap_bytes td patch (unat patch_len)) = rest3 \<and>
		        varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
		        drop (unat (pr_t_C.pos_C vaaaaa))
		          (heap_bytes td patch (unat patch_len)) = rest4 \<and>
		        pop_byte rest4 = Some (0, rest5) \<and>
		        varint_decode rest5 = Some (data_len, rest6) \<and>
		        varint_decode rest6 = Some (inst_len, rest7) \<and>
			        varint_decode rest7 = Some (addr_len, rest8) \<and>
			        alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
			        dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len \<and>
			        unat (val_C vaaaa) = dlen \<and>
			        unat (val_C vaaaaa) = pw_tgt_len win \<and>
			        alen =
			          (if UCAST(8 \<rightarrow> 32)
			                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			              (4 :: 32 word) \<noteq> 0
			           then 4 else 0)"
			      using dec3 drop_rest3 dec4 drop_rest4 di0 dec5 dec6 dec7
			            sizes_ok dlen_exact dlen_val tgt_val adler_len_eq by blast
		  qed
		  have app_no_source_prefix_decodes:
		    "\<And>(td :: lifted_globals) (va :: pr_t_C).
		      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
		      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C va = 0 \<and>
		           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
		           nv = unat (val_C va)) \<Longrightarrow>
		      pr_t_C.err_C va = 0 \<Longrightarrow>
		      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
		      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
		      heap_bytes td patch (unat patch_len) =
		        heap_bytes s patch (unat patch_len) \<Longrightarrow>
		      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
		      UCAST(8 \<rightarrow> 32)
		        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		      (1 :: 32 word) = 0 \<Longrightarrow>
		      \<exists>rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
		        varint_decode
		          (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		            (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3) \<and>
		        varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
		        pop_byte rest4 = Some (0, rest5) \<and>
		        varint_decode rest5 = Some (data_len, rest6) \<and>
		        varint_decode rest6 = Some (inst_len, rest7) \<and>
		        varint_decode rest7 = Some (addr_len, rest8) \<and>
		        alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
		        dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len \<and>
		        alen =
		          (if UCAST(8 \<rightarrow> 32)
		                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		              (4 :: 32 word) \<noteq> 0
		           then 4 else 0)"
		  proof -
		    fix td :: lifted_globals and va :: pr_t_C
		    assume hi4_c:
		      "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
		    assume app_read:
		      "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C va = 0 \<and>
		           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
		           nv = unat (val_C va)"
		    assume app_ok: "pr_t_C.err_C va = 0"
		    assume pos_le: "pr_t_C.pos_C va \<le> patch_len"
		    assume app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
		    assume heap_eq: "heap_bytes td patch (unat patch_len) =
		                     heap_bytes s patch (unat patch_len)"
		    assume k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
		    assume no_source:
		      "UCAST(8 \<rightarrow> 32)
		        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		      (1 :: 32 word) = 0"
		    let ?bs = "heap_bytes s patch (unat patch_len)"
		    let ?k_w = "pr_t_C.pos_C va + val_C va"
		    let ?k = "unat ?k_w"
		    have hi4: "hi AND 4 \<noteq> 0"
		      using hi4_c hi_v ucast_and_4_equiv by simp
		    obtain app_len app_rest where
		      vd: "varint_decode body = Some (app_len, app_rest)"
		      and rest_eq: "rest = drop app_len app_rest"
		      using parse_header_app[unfolded app_bit_def] hi4 by blast
		    have vd_bs: "varint_decode (drop 5 ?bs) = Some (app_len, app_rest)"
		      using vd body_from_drop5 by simp
		    have app_len_eq: "app_len = unat (val_C va)"
		      and pos_eq: "unat (pr_t_C.pos_C va) = unat patch_len - length app_rest"
		      using app_read app_ok vd_bs by auto
		    have pos_drop: "drop (unat (pr_t_C.pos_C va)) ?bs = app_rest"
		      using varint_decode_drop_rest[OF vd_bs] pos_eq by simp
		    have val_le: "val_C va \<le> patch_len - pr_t_C.pos_C va"
		      using app_len_ok by (simp add: word_le_not_less)
		    have k_unat: "?k = unat (pr_t_C.pos_C va) + unat (val_C va)"
		      using val_le pos_le
		      apply (simp add: word_le_nat_alt unat_sub)
		      apply (subst unat_word_ariths(1))
		      using unat_lt2p[of patch_len]
		      apply auto
		      done
		    have rest_at_k: "drop ?k ?bs = rest"
		    proof -
		      have "drop ?k ?bs =
		            drop (unat (val_C va))
		              (drop (unat (pr_t_C.pos_C va)) ?bs)"
		        using k_unat by (simp add: drop_drop add.commute)
		      also have "\<dots> = drop (unat (val_C va)) app_rest"
		        using pos_drop by simp
		      also have "\<dots> = rest"
		        using rest_eq app_len_eq by simp
		      finally show ?thesis .
		    qed
		    have parsed_at_k: "parse_window (drop ?k ?bs) = Inl (win, tail)"
		      using pw rest_at_k by simp
		    have k_lt: "?k < length ?bs"
		      using k_lt_w by (simp add: word_less_nat_alt)
		    have nth_s: "?bs ! ?k = heap_w8 s (patch +\<^sub>p uint ?k_w)"
		      using k_lt by (simp add: heap_bytes_nth)
		    have heap_w8_eq:
		      "heap_w8 td (patch +\<^sub>p uint ?k_w) =
		       heap_w8 s (patch +\<^sub>p uint ?k_w)"
		      using heap_eq k_lt by (auto dest: heap_bytes_eq_heap_w8_uintD)
		    have nth_eq: "?bs ! ?k = heap_w8 td (patch +\<^sub>p uint ?k_w)"
		      using nth_s heap_w8_eq by simp
			    have no_source8: "(?bs ! ?k) AND (1 :: 8 word) = 0"
			    proof -
			      have "heap_w8 td (patch +\<^sub>p uint ?k_w) AND (1 :: 8 word) = 0"
			        using no_source by word_bitwise
			      thus ?thesis using nth_eq by simp
			    qed
			    have adler_len_eq:
			      "(if (?bs ! ?k) AND (0x04 :: 8 word) \<noteq> 0 then 4 else 0) =
			       (if UCAST(8 \<rightarrow> 32)
			             (heap_w8 td (patch +\<^sub>p uint ?k_w)) AND (4 :: 32 word) \<noteq> 0
			        then 4 else 0)"
			    proof -
			      have ucast4:
			        "(UCAST(8 \<rightarrow> 32)
			          (heap_w8 td (patch +\<^sub>p uint ?k_w)) AND (4 :: 32 word) \<noteq> 0) =
			         (heap_w8 td (patch +\<^sub>p uint ?k_w) AND (0x04 :: 8 word) \<noteq> 0)"
			        by word_bitwise
			      show ?thesis using nth_eq ucast4 by simp
			    qed
			    obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len where
		      dec3: "varint_decode (drop (Suc ?k) ?bs) = Some (dlen, rest3)"
		      and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
		      and di0: "pop_byte rest4 = Some (0, rest5)"
		      and dec5: "varint_decode rest5 = Some (data_len, rest6)"
		      and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
		      and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
		      and sizes_ok:
		        "(if (?bs ! ?k) AND (0x04 :: 8 word) \<noteq> 0 then 4 else 0) +
		           data_len + inst_len + addr_len \<le> length rest8"
		      and dlen_exact:
		        "dlen = (length rest3 - length rest8) +
		                (if (?bs ! ?k) AND (0x04 :: 8 word) \<noteq> 0 then 4 else 0) +
		                data_len + inst_len + addr_len"
		      using parse_window_no_source_full_decodes[OF parsed_at_k k_lt no_source8]
		      by blast
		    have k1_unat: "unat (?k_w + 1) = Suc ?k"
		      using unat_x_plus_1[OF k_lt_w] by simp
		    have dec3_td:
		      "varint_decode
		        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		          (heap_bytes td patch (unat patch_len))) =
		       Some (dlen, rest3)"
		      using dec3 k1_unat heap_eq by simp
		    show "\<exists>rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
		        varint_decode
		          (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		            (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3) \<and>
		        varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
		        pop_byte rest4 = Some (0, rest5) \<and>
		        varint_decode rest5 = Some (data_len, rest6) \<and>
		        varint_decode rest6 = Some (inst_len, rest7) \<and>
		        varint_decode rest7 = Some (addr_len, rest8) \<and>
		        alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
		        dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len \<and>
			        alen =
			          (if UCAST(8 \<rightarrow> 32)
			                (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			              (4 :: 32 word) \<noteq> 0
			           then 4 else 0)"
			      using dec3_td dec4 di0 dec5 dec6 dec7 sizes_ok dlen_exact
			            adler_len_eq by blast
		  qed
		  have app_no_source_tgt_decode_some:
		    "\<And>(td :: lifted_globals) (va :: pr_t_C) (vaa :: pr_t_C).
		      UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0 \<Longrightarrow>
		      (case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C va = 0 \<and>
		           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
		           nv = unat (val_C va)) \<Longrightarrow>
		      pr_t_C.err_C va = 0 \<Longrightarrow>
		      pr_t_C.pos_C va \<le> patch_len \<Longrightarrow>
		      \<not> patch_len - pr_t_C.pos_C va < val_C va \<Longrightarrow>
		      heap_bytes td patch (unat patch_len) =
		        heap_bytes s patch (unat patch_len) \<Longrightarrow>
		      pr_t_C.pos_C va + val_C va < patch_len \<Longrightarrow>
		      UCAST(8 \<rightarrow> 32)
		        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		      (1 :: 32 word) = 0 \<Longrightarrow>
		      (case varint_decode
		        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaa = 0 \<and>
		           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaa)) \<Longrightarrow>
		      pr_t_C.err_C vaa = 0 \<Longrightarrow>
		      \<exists>nv rest.
		        varint_decode
		          (drop (unat (pr_t_C.pos_C vaa))
		            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
		  proof -
		    fix td :: lifted_globals and va vaa :: pr_t_C
		    assume hi4_c: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND (4 :: 32 word) \<noteq> 0"
		      and app_read: "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C va = 0 \<and>
		           unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
		           nv = unat (val_C va)"
		      and app_ok: "pr_t_C.err_C va = 0"
		      and pos_le: "pr_t_C.pos_C va \<le> patch_len"
		      and app_len_ok: "\<not> patch_len - pr_t_C.pos_C va < val_C va"
		      and heap_eq: "heap_bytes td patch (unat patch_len) =
		        heap_bytes s patch (unat patch_len)"
		      and k_lt_w: "pr_t_C.pos_C va + val_C va < patch_len"
		      and no_source: "UCAST(8 \<rightarrow> 32)
		        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
		      (1 :: 32 word) = 0"
		      and dlen_read: "case varint_decode
		        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		          (heap_bytes td patch (unat patch_len))) of
		         None \<Rightarrow> pr_t_C.err_C vaa \<noteq> 0
		       | Some (nv, rest) \<Rightarrow>
		           pr_t_C.err_C vaa = 0 \<and>
		           unat (pr_t_C.pos_C vaa) = unat patch_len - length rest \<and>
		           nv = unat (val_C vaa)"
		      and dlen_ok: "pr_t_C.err_C vaa = 0"
		    obtain rest3 rest4 where
		      dec3: "varint_decode
		        (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		          (heap_bytes td patch (unat patch_len))) = Some (unat (val_C vaa), rest3)"
		      and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
		      using app_no_source_prefix_decodes[OF hi4_c app_read app_ok pos_le app_len_ok
		        heap_eq k_lt_w no_source] dlen_read dlen_ok
		      by (auto split: option.splits)
		    have pos_vaa:
		      "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest3"
		      using dlen_read dlen_ok dec3 by simp
		    have drop_rest3:
		      "drop (unat (pr_t_C.pos_C vaa))
		        (heap_bytes td patch (unat patch_len)) = rest3"
		      using varint_decode_drop_rest[OF dec3] pos_vaa by simp
		    show "\<exists>nv rest.
		        varint_decode
		          (drop (unat (pr_t_C.pos_C vaa))
		            (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
		      using dec4 drop_rest3 by simp
		  qed
		  let ?Post = "\<lambda>r t. r = Result (0 :: int) \<and>
		                     unat (heap_w32 t out_len) = length tgt \<and>
		                     heap_bytes t out (length tgt) = tgt"
  have "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s \<lbrace> ?Post \<rbrace>"
  proof -
    show ?thesis
      unfolding vcdiff_decode'_def
      supply read_byte'_spec [runs_to_vcg]
      supply read_varint'_spec [runs_to_vcg]
      supply near_init_preserves_setup_word
          [where patch = patch and patch_n = "unat patch_len"
             and src = src and src_n = "unat src_len" and out_len = out_len,
           runs_to_vcg]
      supply same_init_preserves_setup_word
          [where patch = patch and patch_n = "unat patch_len"
             and src = src and src_n = "unat src_len" and out_len = out_len,
           runs_to_vcg]
      supply build_code_table'_setup
        [where patch = patch and patch_n = "unat patch_len"
           and src = src and src_n = "unat src_len" and out_len = out_len,
         runs_to_vcg]
      supply decode_address'_spec [runs_to_vcg]
      supply add_loop_correct [runs_to_vcg]
      supply run_loop_correct [runs_to_vcg]
      supply copy_loop_correct [runs_to_vcg]
      supply if_split [split del]
      apply runs_to_vcg
      \<comment> \<open>Close subgoals 1-14: ptr_valid, magic-byte mismatches, hdr bit,
          length bounds.  For IS_VALID we invoke patchi_ok; for magic
          mismatches we use the magicK_v facts extracted from Inl.\<close>
      subgoal using out_len_ok by simp
      subgoal using len_ge5 by (simp add: word_less_nat_alt)
      subgoal using patchi_ok[of 0] by simp
      subgoal using magic0_v by simp
      subgoal using patchi_ok[of 1] by simp
      subgoal using magic1_v by simp
      subgoal using patchi_ok[of 2] by simp
      subgoal using magic2_v by simp
      subgoal using patchi_ok[of 3] by simp
      subgoal using magic3_v by simp
      subgoal using patchi_ok[of 4] by simp
      subgoal premises prems
        \<comment> \<open>Goal: UCAST(hi) AND 3 ≠ 0 ⟹ False.\<close>
      proof -
        have eq: "UCAST(8 \<rightarrow> 32) hi AND 3 = UCAST(8 \<rightarrow> 32) (hi AND 3)"
          by word_bitwise
        from prems eq hi_v hdr3 show ?thesis by auto
      qed
	      subgoal using patch_ok by simp
	      subgoal using len_ge5_word by simp
	      \<comment> \<open>Remaining: 8 subgoals.  Subgoals 1-4 are the app-header branch with
	          varint-error path — contradiction from Inl (spec requires varint success).
	          Subgoals 5-8 are the main body with build_code_table'.\<close>
      \<comment> \<open>Subgoals 1-4: contradiction from err ≠ 0 + Inl ⟹ varint succeeds.\<close>
      subgoal for va
        using parse_header_app[unfolded app_bit_def] ucast_and_4_equiv
              body_from_drop5 hi_v
        by (auto split: option.splits)
      subgoal for va
        using parse_header_app[unfolded app_bit_def] ucast_and_4_equiv
              body_from_drop5 hi_v
        by (auto split: option.splits)
      subgoal for va
        using parse_header_app[unfolded app_bit_def] ucast_and_4_equiv
              body_from_drop5 hi_v
        by (auto split: option.splits)
      \<comment> \<open>Subgoal 4: patch_len - pos < val_C ⟹ False.  Need: the spec
          succeeded with rest = drop app_len rest', hence app_len ≤ length rest',
          hence pos + app_len ≤ patch_len (i.e. val_C ≤ patch_len - pos).\<close>
      subgoal for va
      proof -
        assume err0: "pr_t_C.err_C va = 0"
           and lt: "patch_len - pr_t_C.pos_C va < val_C va"
           and app4: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 4 \<noteq> 0"
           and pos_ge5: "5 \<le> pr_t_C.pos_C va"
           and pos_le: "pr_t_C.pos_C va \<le> patch_len"
           and case_split:
             "case varint_decode (drop 5 (heap_bytes s patch (unat patch_len))) of
                None \<Rightarrow> pr_t_C.err_C va \<noteq> 0
              | Some (nv, rest) \<Rightarrow> pr_t_C.err_C va = 0 \<and>
                  unat (pr_t_C.pos_C va) = unat patch_len - length rest \<and>
                  nv = unat (val_C va)"
        have hi4: "hi AND 4 \<noteq> 0" using app4 hi_v ucast_and_4_equiv by simp
        obtain app_len rest' where
          vd: "varint_decode body = Some (app_len, rest')" and
          al_le: "app_len \<le> length rest'"
          using parse_header_app[unfolded app_bit_def] hi4 by blast
        have vd': "varint_decode (drop 5 (heap_bytes s patch (unat patch_len)))
                  = Some (app_len, rest')"
          using vd body_from_drop5 by simp
        from case_split vd'
        have err_ok: "pr_t_C.err_C va = 0"
          and pos_eq: "unat (pr_t_C.pos_C va) = unat patch_len - length rest'"
          and nv_eq: "app_len = unat (val_C va)"
          by auto
        have unat_sub_eq: "unat (patch_len - pr_t_C.pos_C va)
                        = unat patch_len - unat (pr_t_C.pos_C va)"
          using pos_le by (rule unat_sub)
        have "unat (val_C va) = app_len" using nv_eq by simp
        also have "app_len \<le> length rest'" using al_le .
        also have "length rest' = unat patch_len - unat (pr_t_C.pos_C va)"
        proof -
          have "length rest' \<le> length (heap_bytes s patch (unat patch_len))"
            using varint_decode_length[OF vd'] by simp
          hence "length rest' \<le> unat patch_len" by simp
          thus ?thesis using pos_eq by arith
        qed
        also have "\<dots> = unat (patch_len - pr_t_C.pos_C va)"
          using unat_sub_eq by simp
        finally have "unat (val_C va) \<le> unat (patch_len - pr_t_C.pos_C va)" .
        with lt show False by (simp add: word_less_nat_alt)
      qed
      \<comment> \<open>Subgoals 5-8: main body.  First subgoal:
            code_tbl_built = 0, app-header present, no-source path.
          After runs_to_vcg fires build_code_table'_spec + init-loop
          preservations, we're at the win_ind read_byte' with clean
          hypotheses (taa_, ta_, t_ form a chain with heap_bytes and
          buf_valid preserved).  Close via read_byte'_spec unfold.\<close>
      subgoal for va tb tc td
        apply runs_to_vcg
        \<comment> \<open>Establish word-level bound: pos_C va + val_C va ≤ patch_len.\<close>
        apply (subgoal_tac "pr_t_C.pos_C va + val_C va \<le> patch_len")
         prefer 2
         subgoal
           \<comment> \<open>From the C's check: val_C va ≤ patch_len - pos_C va.  Thus
               pos_C va + val_C va ≤ patch_len (word-level, no overflow
               since pos_C va ≤ patch_len).\<close>
           apply (subgoal_tac "val_C va \<le> patch_len - pr_t_C.pos_C va")
            prefer 2
            apply (simp add: word_le_not_less)
           apply (simp add: word_le_nat_alt unat_sub)
           apply (subst unat_word_ariths(1))
           using unat_lt2p[of patch_len]
           apply auto
           done
        \<comment> \<open>Derive buf_valid td patch (unat patch_len) from chain:
            heap_typing td = heap_typing s (via build_code_table'_preserves_typing
            + init-loop preservations) ⟹ buf_valid td = buf_valid s.\<close>
        apply (subgoal_tac "buf_valid td patch (unat patch_len)")
         prefer 2
         using patch_ok apply (simp add: buf_valid_def)
        \<comment> \<open>Provide witness via read_byte'_spec.\<close>
        apply (subst read_byte'_spec)
         subgoal
           apply (rule impI)
           apply (erule buf_valid_uintD)
           apply (simp add: word_less_nat_alt word_le_nat_alt)
           done
        \<comment> \<open>Provide witness: the if-expression itself.  Then split on
            the condition and handle each case.\<close>
        apply clarsimp
        apply (split if_splits)
        apply (intro conjI impI)
         \<comment> \<open>Two subgoals: success (pos+val < patch_len) and truncation
             (= patch_len).  Both deferred until the outer whileLoop is
             reachable.\<close>
         apply (all \<open>clarsimp?\<close>)
         subgoal \<comment> \<open>success branch: runs_to_vcg advances through the
             win_ind checks + varint chain + inner whileLoops, leaving
             31 subgoals covering:
             * win_ind bit checks (contradictions from parse_window)
             * varint chain side conditions (ptr_valid, bounds)
             * the outer instruction-dispatch whileLoop (the main work)
             * post-loop cursor consistency checks
             * final out_len write.
             Deferred — see planning/refine-progress.md for the strengthened
             decode_loop_inv approach.\<close>
           apply runs_to_vcg
           subgoal premises prems
           proof -
             let ?bs = "heap_bytes s patch (unat patch_len)"
             let ?k_w = "pr_t_C.pos_C va + val_C va"
             let ?k = "unat ?k_w"
             have hi4: "hi AND 4 \<noteq> 0"
               using prems hi_v ucast_and_4_equiv by simp
             obtain app_len app_rest where
               vd: "varint_decode body = Some (app_len, app_rest)"
               and app_len_le: "app_len \<le> length app_rest"
               and rest_eq: "rest = drop app_len app_rest"
               using parse_header_app[unfolded app_bit_def] hi4 by blast
             have vd_bs: "varint_decode (drop 5 ?bs) = Some (app_len, app_rest)"
               using vd body_from_drop5 by simp
             have app_len_eq: "app_len = unat (val_C va)"
               and pos_eq: "unat (pr_t_C.pos_C va) = unat patch_len - length app_rest"
               using prems vd_bs by auto
             have pos_drop: "drop (unat (pr_t_C.pos_C va)) ?bs = app_rest"
               using varint_decode_drop_rest[OF vd_bs] pos_eq by simp
             have val_le: "val_C va \<le> patch_len - pr_t_C.pos_C va"
               using prems by (simp add: word_le_not_less)
             have k_unat: "?k = unat (pr_t_C.pos_C va) + unat (val_C va)"
               using val_le prems
               apply (simp add: word_le_nat_alt unat_sub)
               apply (subst unat_word_ariths(1))
               using unat_lt2p[of patch_len]
               apply auto
               done
             have rest_at_k: "drop ?k ?bs = rest"
             proof -
               have "drop ?k ?bs =
                     drop (unat (val_C va))
                       (drop (unat (pr_t_C.pos_C va)) ?bs)"
                 using k_unat by (simp add: drop_drop add.commute)
               also have "\<dots> = drop (unat (val_C va)) app_rest"
                 using pos_drop by simp
               also have "\<dots> = rest"
                 using rest_eq app_len_eq by simp
               finally show ?thesis .
             qed
             have parsed_at_k: "parse_window (drop ?k ?bs) = Inl (win, tail)"
               using pw rest_at_k by simp
             have k_lt: "?k < length ?bs"
               using prems by (simp add: word_less_nat_alt)
             have bit_clear: "(?bs ! ?k) AND 0x02 = 0"
               by (rule parse_window_drop_byte_bits(1)[OF parsed_at_k k_lt])
             have nth_eq: "?bs ! ?k = heap_w8 s (patch +\<^sub>p uint ?k_w)"
               using k_lt by (simp add: heap_bytes_nth)
             have heap_eq: "heap_w8 td (patch +\<^sub>p uint ?k_w) =
                            heap_w8 s (patch +\<^sub>p uint ?k_w)"
               using prems k_lt by (auto dest: heap_bytes_eq_heap_w8_uintD)
             have byte_clear:
               "heap_w8 s (patch +\<^sub>p uint ?k_w) AND (2 :: 8 word) = 0"
               using bit_clear nth_eq by simp
             have bit_clear32:
               "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint ?k_w)) AND
                (2 :: 32 word) = 0"
             proof -
               have "UCAST(8 \<rightarrow> 32)
                       (heap_w8 s (patch +\<^sub>p uint ?k_w) AND (2 :: 8 word))
                     = (0 :: 32 word)"
                 using byte_clear by simp
               moreover have "UCAST(8 \<rightarrow> 32)
                       (heap_w8 s (patch +\<^sub>p uint ?k_w) AND (2 :: 8 word))
                     = UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint ?k_w)) AND
                       (2 :: 32 word)"
                 by word_bitwise
               ultimately show ?thesis by simp
             qed
             show False
               using prems bit_clear32 heap_eq by simp
           qed
           subgoal premises prems
           proof -
             let ?bs = "heap_bytes s patch (unat patch_len)"
             let ?k_w = "pr_t_C.pos_C va + val_C va"
             let ?k = "unat ?k_w"
             have hi4: "hi AND 4 \<noteq> 0"
               using prems hi_v ucast_and_4_equiv by simp
             obtain app_len app_rest where
               vd: "varint_decode body = Some (app_len, app_rest)"
               and app_len_le: "app_len \<le> length app_rest"
               and rest_eq: "rest = drop app_len app_rest"
               using parse_header_app[unfolded app_bit_def] hi4 by blast
             have vd_bs: "varint_decode (drop 5 ?bs) = Some (app_len, app_rest)"
               using vd body_from_drop5 by simp
             have app_len_eq: "app_len = unat (val_C va)"
               and pos_eq: "unat (pr_t_C.pos_C va) = unat patch_len - length app_rest"
               using prems vd_bs by auto
             have pos_drop: "drop (unat (pr_t_C.pos_C va)) ?bs = app_rest"
               using varint_decode_drop_rest[OF vd_bs] pos_eq by simp
             have val_le: "val_C va \<le> patch_len - pr_t_C.pos_C va"
               using prems by (simp add: word_le_not_less)
             have k_unat: "?k = unat (pr_t_C.pos_C va) + unat (val_C va)"
               using val_le prems
               apply (simp add: word_le_nat_alt unat_sub)
               apply (subst unat_word_ariths(1))
               using unat_lt2p[of patch_len]
               apply auto
               done
             have rest_at_k: "drop ?k ?bs = rest"
             proof -
               have "drop ?k ?bs =
                     drop (unat (val_C va))
                       (drop (unat (pr_t_C.pos_C va)) ?bs)"
                 using k_unat by (simp add: drop_drop add.commute)
               also have "\<dots> = drop (unat (val_C va)) app_rest"
                 using pos_drop by simp
               also have "\<dots> = rest"
                 using rest_eq app_len_eq by simp
               finally show ?thesis .
             qed
             have parsed_at_k: "parse_window (drop ?k ?bs) = Inl (win, tail)"
               using pw rest_at_k by simp
             have k_lt: "?k < length ?bs"
               using prems by (simp add: word_less_nat_alt)
             have bit_clear: "(?bs ! ?k) AND 0xFA = 0"
               by (rule parse_window_drop_byte_bits(2)[OF parsed_at_k k_lt])
             have nth_eq: "?bs ! ?k = heap_w8 s (patch +\<^sub>p uint ?k_w)"
               using k_lt by (simp add: heap_bytes_nth)
             have heap_eq: "heap_w8 td (patch +\<^sub>p uint ?k_w) =
                            heap_w8 s (patch +\<^sub>p uint ?k_w)"
               using prems k_lt by (auto dest: heap_bytes_eq_heap_w8_uintD)
             have byte_clear:
               "heap_w8 s (patch +\<^sub>p uint ?k_w) AND (0xFA :: 8 word) = 0"
               using bit_clear nth_eq by simp
             have bit_clear32:
               "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint ?k_w)) AND
                (0xFFFFFFFA :: 32 word) = 0"
             proof -
               have low_mask:
                 "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint ?k_w)) AND
                  (0xFA :: 32 word) = 0"
               proof -
                 have "UCAST(8 \<rightarrow> 32)
                         (heap_w8 s (patch +\<^sub>p uint ?k_w) AND (0xFA :: 8 word))
                       = (0 :: 32 word)"
                   using byte_clear by simp
                 moreover have "UCAST(8 \<rightarrow> 32)
                         (heap_w8 s (patch +\<^sub>p uint ?k_w) AND (0xFA :: 8 word))
                       = UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint ?k_w)) AND
                         (0xFA :: 32 word)"
                   by word_bitwise
                 ultimately show ?thesis by simp
               qed
               have mask_eq:
                 "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint ?k_w)) AND
                  (0xFFFFFFFA :: 32 word) =
                  UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint ?k_w)) AND
                  (0xFA :: 32 word)"
                 by word_bitwise
               show ?thesis using low_mask mask_eq by simp
             qed
	             show False
	               using prems bit_clear32 heap_eq by simp
	           qed
	           subgoal using src_nonnull by simp
	           subgoal by (rule word_plus_one_le_of_less; simp)
	           subgoal premises prems for vaa
	           proof -
	             let ?bs = "heap_bytes s patch (unat patch_len)"
	             let ?k_w = "pr_t_C.pos_C va + val_C va"
	             let ?k = "unat ?k_w"
	             have hi4: "hi AND 4 \<noteq> 0"
	               using prems hi_v ucast_and_4_equiv by simp
	             obtain app_len app_rest where
	               vd: "varint_decode body = Some (app_len, app_rest)"
	               and rest_eq: "rest = drop app_len app_rest"
	               using parse_header_app[unfolded app_bit_def] hi4 by blast
	             have vd_bs: "varint_decode (drop 5 ?bs) = Some (app_len, app_rest)"
	               using vd body_from_drop5 by simp
	             have app_len_eq: "app_len = unat (val_C va)"
	               and pos_eq: "unat (pr_t_C.pos_C va) = unat patch_len - length app_rest"
	               using prems vd_bs by auto
	             have pos_drop: "drop (unat (pr_t_C.pos_C va)) ?bs = app_rest"
	               using varint_decode_drop_rest[OF vd_bs] pos_eq by simp
	             have val_le: "val_C va \<le> patch_len - pr_t_C.pos_C va"
	               using prems by (simp add: word_le_not_less)
	             have k_unat: "?k = unat (pr_t_C.pos_C va) + unat (val_C va)"
	               using val_le prems
	               apply (simp add: word_le_nat_alt unat_sub)
	               apply (subst unat_word_ariths(1))
	               using unat_lt2p[of patch_len]
	               apply auto
	               done
	             have rest_at_k: "drop ?k ?bs = rest"
	             proof -
	               have "drop ?k ?bs =
	                     drop (unat (val_C va))
	                       (drop (unat (pr_t_C.pos_C va)) ?bs)"
	                 using k_unat by (simp add: drop_drop add.commute)
	               also have "\<dots> = drop (unat (val_C va)) app_rest"
	                 using pos_drop by simp
	               also have "\<dots> = rest"
	                 using rest_eq app_len_eq by simp
	               finally show ?thesis .
	             qed
	             have parsed_at_k: "parse_window (drop ?k ?bs) = Inl (win, tail)"
	               using pw rest_at_k by simp
	             have k_lt: "?k < length ?bs"
	               using prems by (simp add: word_less_nat_alt)
	             have nth_eq: "?bs ! ?k = heap_w8 s (patch +\<^sub>p uint ?k_w)"
	               using k_lt by (simp add: heap_bytes_nth)
	             have heap_eq: "heap_w8 td (patch +\<^sub>p uint ?k_w) =
	                            heap_w8 s (patch +\<^sub>p uint ?k_w)"
	               using prems k_lt by (auto dest: heap_bytes_eq_heap_w8_uintD)
	             have source_set8: "(?bs ! ?k) AND (1 :: 8 word) \<noteq> 0"
	             proof -
	               have "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p uint ?k_w)) AND
	                     (1 :: 32 word) = 1"
	                 using prems heap_eq by simp
	               hence "heap_w8 s (patch +\<^sub>p uint ?k_w) AND (1 :: 8 word) \<noteq> 0"
	                 by word_bitwise
	               thus ?thesis using nth_eq by simp
	             qed
	             obtain rest1 rest2 rest3 dlen where
	               dec1: "varint_decode (drop (Suc ?k) ?bs) =
	                        Some (pw_src_seg_len win, rest1)"
	               and dec2: "varint_decode rest1 = Some (pw_src_seg_off win, rest2)"
	               and dec3: "varint_decode rest2 = Some (dlen, rest3)"
	               using parse_window_source_prefix_decodes[OF parsed_at_k k_lt source_set8]
	               by blast
	             have k1_unat: "unat (?k_w + 1) = Suc ?k"
	             proof -
	               have "?k_w < patch_len" using prems by simp
	               hence "unat (?k_w + 1) = unat ?k_w + 1"
	                 by (rule unat_x_plus_1)
	               thus ?thesis by simp
	             qed
	             have dec1_td:
	               "varint_decode
	                  (drop (unat (?k_w + 1))
	                    (heap_bytes td patch (unat patch_len))) =
	                Some (pw_src_seg_len win, rest1)"
	               using dec1 k1_unat prems by simp
	             show ?thesis
	               using prems dec1_td by simp
	           qed
	           subgoal premises prems for vaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_len_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_len_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C va + val_C va + 1))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa vaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_off_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa vaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_off_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa vaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_off_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa vaaa
	           proof -
	             have vals:
	               "unat (val_C vaa) = pw_src_seg_len win \<and>
	                unat (val_C vaaa) = pw_src_seg_off win"
	               apply (rule app_source_values
	                 [where td = td and va = va and vaa = vaa and vaaa = vaaa])
	               using prems apply simp_all
	               done
	             have "unat (val_C vaaa) \<le> unat src_len"
	               using vals win_src_bounds by simp
	             with prems show False
	               by (simp add: word_less_nat_alt)
	           qed
	           subgoal premises prems for vaa vaaa
	           proof -
	             have vals:
	               "unat (val_C vaa) = pw_src_seg_len win \<and>
	                unat (val_C vaaa) = pw_src_seg_off win"
	               apply (rule app_source_values
	                 [where td = td and va = va and vaa = vaa and vaaa = vaaa])
	               using prems apply simp_all
	               done
	             have off_le_word: "val_C vaaa \<le> src_len"
	               using vals win_src_bounds by (simp add: word_le_nat_alt)
	             have len_le:
	               "unat (val_C vaa) \<le> unat src_len - unat (val_C vaaa)"
	               using vals win_src_bounds by simp
	             have "val_C vaa \<le> src_len - val_C vaaa"
	               using len_le off_le_word by (simp add: word_le_nat_alt unat_sub)
	             with prems show False
	               by (simp add: word_le_not_less)
	           qed
	           subgoal premises prems for vaa vaaa vaaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_dlen_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa vaaa vaaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_dlen_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa vaaa vaaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_dlen_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
		           subgoal premises prems for vaa vaaa vaaaa
		           proof -
		             have stage:
		               "\<exists>rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen.
		                  varint_decode
		                    (drop (unat (pr_t_C.pos_C vaaa))
		                      (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3) \<and>
		                  varint_decode rest3 = Some (pw_tgt_len win, rest4) \<and>
		                  pop_byte rest4 = Some (0, rest5) \<and>
		                  varint_decode rest5 = Some (data_len, rest6) \<and>
		                  varint_decode rest6 = Some (inst_len, rest7) \<and>
		                  varint_decode rest7 = Some (addr_len, rest8) \<and>
		                  alen + data_len + inst_len + addr_len \<le> length rest8 \<and>
		                  dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len"
			               using app_source_dlen_stage[where td=td and va=va and vaa=vaa and vaaa=vaaa]
			                     prems by blast
		             then obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
		               dec3: "varint_decode
		                 (drop (unat (pr_t_C.pos_C vaaa))
		                   (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3)"
		               and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
		               and di0: "pop_byte rest4 = Some (0, rest5)"
		               and dec5: "varint_decode rest5 = Some (data_len, rest6)"
		               and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
		               and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
		               and sizes_ok: "alen + data_len + inst_len + addr_len \<le> length rest8"
		               and dlen_exact:
		                 "dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len"
		               by blast
		             have rest8_le_rest3: "length rest8 \<le> length rest3"
		             proof -
		               have "length rest4 \<le> length rest3"
		                 by (rule varint_decode_length[OF dec4])
		               moreover have "length rest5 < length rest4"
		               proof -
		                 have "rest4 \<noteq> []"
		                 proof
		                   assume "rest4 = []"
		                   with di0 show False
		                     by (simp add: pop_byte_def)
		                 qed
		                 then obtain a rs where rest4_eq: "rest4 = a # rs"
		                   by (cases rest4) auto
		                 moreover have "rest5 = rs"
		                   using di0 rest4_eq by (simp add: pop_byte_def)
		                 ultimately show ?thesis by simp
		               qed
		               moreover have "length rest6 \<le> length rest5"
		                 by (rule varint_decode_length[OF dec5])
		               moreover have "length rest7 \<le> length rest6"
		                 by (rule varint_decode_length[OF dec6])
		               moreover have "length rest8 \<le> length rest7"
		                 by (rule varint_decode_length[OF dec7])
		               ultimately show ?thesis by arith
		             qed
		             have dlen_le: "dlen \<le> length rest3"
		               using sizes_ok dlen_exact rest8_le_rest3 by arith
	             have val_eq: "unat (val_C vaaaa) = dlen"
	               using prems dec3 by simp
	             have pos_eq: "unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest3"
	               using prems dec3 by simp
		             have rem_eq: "unat (patch_len - pr_t_C.pos_C vaaaa) = length rest3"
		             proof -
		               have "unat (patch_len - pr_t_C.pos_C vaaaa) =
		                     unat patch_len - unat (pr_t_C.pos_C vaaaa)"
		                 using prems by (simp add: unat_sub word_le_nat_alt)
		               also have "\<dots> = length rest3"
		               proof -
		                 have "length rest3 \<le> unat patch_len"
		                 proof -
		                   have "length rest3 \<le>
		                         length (drop (unat (pr_t_C.pos_C vaaa))
		                           (heap_bytes td patch (unat patch_len)))"
		                     by (rule varint_decode_length[OF dec3])
		                   also have "\<dots> \<le> unat patch_len"
		                     by simp
		                   finally show ?thesis .
		                 qed
		                 with pos_eq show ?thesis by arith
		               qed
		               finally show ?thesis .
		             qed
	             have "val_C vaaaa \<le> patch_len - pr_t_C.pos_C vaaaa"
	               using dlen_le val_eq rem_eq by (simp add: word_le_nat_alt)
	             with prems show False
	               by (simp add: word_le_not_less)
	           qed
	           subgoal premises prems for vaa vaaa vaaaa vaaaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaaaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_tgt_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaaaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa vaaa vaaaa vaaaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaaaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_tgt_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaaaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
	           subgoal premises prems for vaa vaaa vaaaa vaaaaa
	           proof -
	             have some:
	               "\<exists>nv rest.
	                  varint_decode
	                    (drop (unat (pr_t_C.pos_C vaaaa))
	                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
	               apply (rule app_source_tgt_decode_some)
	               using prems apply simp_all
	               done
	             then obtain nv rest' where dec:
	               "varint_decode
	                  (drop (unat (pr_t_C.pos_C vaaaa))
	                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
	               by blast
	             have "pr_t_C.err_C vaaaaa = 0"
	               using prems dec by simp
	             with prems show ?thesis by simp
	           qed
		           subgoal premises prems for vaa vaaa vaaaa vaaaaa
		           proof -
		             have tgt_val: "unat (val_C vaaaaa) = pw_tgt_len win"
		               apply (rule app_source_tgt_value[where td=td])
		               using prems apply simp_all
		               done
	             have "length tgt \<le> unat out_cap"
	               using out_cap_enough Inl by simp
	             hence "unat (val_C vaaaaa) \<le> unat out_cap"
	               using tgt_val tgt_len_eq by simp
		             hence "val_C vaaaaa \<le> out_cap"
		               by (simp add: word_le_nat_alt)
		             moreover have "unat (val_C vaaaaa) \<le> unat out_cap"
		               using calculation by (simp add: word_le_nat_alt)
			             ultimately show False
			               using prems by simp
				           qed
		           subgoal premises prems for vaa vaaa vaaaa vaaaaa
		           proof -
		             obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
		               dec3: "varint_decode
		                 (drop (unat (pr_t_C.pos_C vaaa))
		                   (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3)"
		               and drop_rest3:
		                 "drop (unat (pr_t_C.pos_C vaaaa))
		                   (heap_bytes td patch (unat patch_len)) = rest3"
		               and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
		               and drop_rest4:
		                 "drop (unat (pr_t_C.pos_C vaaaaa))
		                   (heap_bytes td patch (unat patch_len)) = rest4"
		               and di0: "pop_byte rest4 = Some (0, rest5)"
		               and dec5: "varint_decode rest5 = Some (data_len, rest6)"
		               and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
		               and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
		               and sizes_ok:
		                 "alen + data_len + inst_len + addr_len \<le> length rest8"
			               and dlen_exact:
			                 "dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len"
			               and dlen_val: "unat (val_C vaaaa) = dlen"
			               and tgt_val: "unat (val_C vaaaaa) = pw_tgt_len win"
			               and alen_eq:
			                 "alen =
			                   (if UCAST(8 \<rightarrow> 32)
			                         (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			                       (4 :: 32 word) \<noteq> 0
			                    then 4 else 0)"
			               using app_source_payload_stage[where td=td and va=va
			                 and vaa=vaa and vaaa=vaaa and vaaaa=vaaaa and vaaaaa=vaaaaa]
			                     prems by blast
		             have rest4_cons: "rest4 = 0 # rest5"
		               using di0 by (cases rest4) (simp_all add: pop_byte_def)
		             let ?di_pos = "pr_t_C.pos_C vaaaaa"
		             let ?bs_td = "heap_bytes td patch (unat patch_len)"
		             have di_pos_lt_nat: "unat ?di_pos < unat patch_len"
		             proof -
		               have "drop (unat ?di_pos) ?bs_td \<noteq> []"
		                 using drop_rest4 rest4_cons by simp
		               thus ?thesis by (simp add: drop_eq_Nil)
		             qed
		             have di_pos_lt: "?di_pos < patch_len"
		               using di_pos_lt_nat by (simp add: word_less_nat_alt)
		             have heap_di0:
		               "heap_w8 td (patch +\<^sub>p uint ?di_pos) = 0"
		             proof -
		               have "?bs_td ! unat ?di_pos = 0"
		               proof -
		                 have "?bs_td ! unat ?di_pos =
		                       drop (unat ?di_pos) ?bs_td ! 0"
		                   using di_pos_lt_nat by (simp add: nth_drop)
		                 also have "\<dots> = 0"
		                   using drop_rest4 rest4_cons by simp
		                 finally show ?thesis .
		               qed
		               thus ?thesis
		                 using di_pos_lt_nat by (simp add: heap_bytes_nth)
		             qed
		             have ptr_di:
		               "ptr_valid (heap_typing td) (patch +\<^sub>p uint ?di_pos)"
		               using prems di_pos_lt_nat
		               by (auto simp: buf_valid_def)
		             have read_di:
		               "read_byte' patch patch_len ?di_pos td =
		                Some (pr_t_C (?di_pos + 1) 0 VCD_OK)"
		             proof -
		               have ptr_imp:
		                 "?di_pos < patch_len \<longrightarrow>
		                  ptr_valid (heap_typing td) (patch +\<^sub>p uint ?di_pos)"
		                 using ptr_di by simp
		               show ?thesis
		                 using read_byte'_spec[OF ptr_imp] di_pos_lt heap_di0 by simp
		             qed
		             have di_pos_suc:
		               "unat (?di_pos + 1) = Suc (unat ?di_pos)"
		               using unat_x_plus_1[OF di_pos_lt] by simp
		             have drop_rest5:
		               "drop (unat (?di_pos + 1)) ?bs_td = rest5"
		             proof -
		               have "drop (Suc (unat ?di_pos)) ?bs_td =
		                     tl (drop (unat ?di_pos) ?bs_td)"
		                 by (simp add: drop_Suc tl_drop)
		               also have "\<dots> = rest5"
		                 using drop_rest4 rest4_cons by simp
		               finally show ?thesis
		                 using di_pos_suc by simp
		             qed
		             have dec5_td:
		               "varint_decode (drop (unat (?di_pos + 1)) ?bs_td) =
		                Some (data_len, rest6)"
		               using dec5 drop_rest5 by simp
		             have rest8_le_rest3: "length rest8 \<le> length rest3"
		             proof -
		               have "length rest4 \<le> length rest3"
		                 by (rule varint_decode_length[OF dec4])
		               moreover have "length rest5 < length rest4"
		               proof -
		                 have "rest4 \<noteq> []"
		                   using rest4_cons by simp
		                 then show ?thesis using rest4_cons by simp
		               qed
		               moreover have "length rest6 \<le> length rest5"
		                 by (rule varint_decode_length[OF dec5])
		               moreover have "length rest7 \<le> length rest6"
		                 by (rule varint_decode_length[OF dec6])
		               moreover have "length rest8 \<le> length rest7"
		                 by (rule varint_decode_length[OF dec7])
		               ultimately show ?thesis by arith
		             qed
		             show ?thesis
		               apply (rule exI[where x = "pr_t_C (?di_pos + 1) 0 VCD_OK"])
		               apply (intro conjI)
		                apply (rule read_di)
		               apply simp
		               apply runs_to_vcg
		               subgoal using prems by simp
		               subgoal using di_pos_lt by (rule word_plus_one_le_of_less)
		               subgoal using dec5_td by simp
		               subgoal using dec5_td by simp
		               subgoal using dec5_td by simp
		               subgoal using prems by simp
		               subgoal premises q for vab vaba
		               proof -
		                 have pos_vab:
		                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
		                   using q dec5_td by simp
		                 have drop_rest6:
		                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
		                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
		                 have dec6_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
		                    Some (inst_len, rest7)"
		                   using dec6 drop_rest6 by simp
		                 show ?thesis using q dec6_td by simp
		               qed
		               subgoal premises q for vab vaba
		               proof -
		                 have pos_vab:
		                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
		                   using q dec5_td by simp
		                 have drop_rest6:
		                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
		                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
		                 have dec6_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
		                    Some (inst_len, rest7)"
		                   using dec6 drop_rest6 by simp
		                 show ?thesis using q dec6_td by simp
		               qed
		               subgoal premises q for vab vaba
		               proof -
		                 have pos_vab:
		                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
		                   using q dec5_td by simp
		                 have drop_rest6:
		                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
		                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
		                 have dec6_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
		                    Some (inst_len, rest7)"
		                   using dec6 drop_rest6 by simp
		                 show ?thesis using q dec6_td by simp
		               qed
		               subgoal using prems by simp
		               subgoal premises q for vab vaba vabaa
		               proof -
		                 have pos_vab:
		                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
		                   using q dec5_td by simp
		                 have drop_rest6:
		                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
		                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
		                 have dec6_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
		                    Some (inst_len, rest7)"
		                   using dec6 drop_rest6 by simp
		                 have pos_vaba:
		                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
		                   using q dec6_td by simp
		                 have drop_rest7:
		                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
		                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
		                 have dec7_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
		                    Some (addr_len, rest8)"
		                   using dec7 drop_rest7 by simp
		                 show ?thesis using q dec7_td by simp
		               qed
		               subgoal premises q for vab vaba vabaa
		               proof -
		                 have pos_vab:
		                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
		                   using q dec5_td by simp
		                 have drop_rest6:
		                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
		                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
		                 have dec6_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
		                    Some (inst_len, rest7)"
		                   using dec6 drop_rest6 by simp
		                 have pos_vaba:
		                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
		                   using q dec6_td by simp
		                 have drop_rest7:
		                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
		                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
		                 have dec7_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
		                    Some (addr_len, rest8)"
		                   using dec7 drop_rest7 by simp
		                 show ?thesis using q dec7_td by simp
		               qed
		               subgoal premises q for vab vaba vabaa
		               proof -
		                 have pos_vab:
		                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
		                   using q dec5_td by simp
		                 have drop_rest6:
		                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
		                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
		                 have dec6_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
		                    Some (inst_len, rest7)"
		                   using dec6 drop_rest6 by simp
		                 have pos_vaba:
		                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
		                   using q dec6_td by simp
		                 have drop_rest7:
		                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
		                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
		                 have dec7_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
		                    Some (addr_len, rest8)"
		                   using dec7 drop_rest7 by simp
		                 show ?thesis using q dec7_td by simp
		               qed
		               subgoal premises q for vab vaba vabaa
		               proof -
		                 have pos_vaaaa:
		                   "unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest3"
		                   using prems dec3 by simp
		                 have pos_vab:
		                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
		                   using q dec5_td by simp
		                 have drop_rest6:
		                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
		                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
		                 have dec6_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
		                    Some (inst_len, rest7)"
		                   using dec6 drop_rest6 by simp
		                 have pos_vaba:
		                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
		                   using q dec6_td by simp
		                 have drop_rest7:
		                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
		                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
		                 have dec7_td:
		                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
		                    Some (addr_len, rest8)"
		                   using dec7 drop_rest7 by simp
				                 have pos_vabaa:
				                   "unat (pr_t_C.pos_C vabaa) = unat patch_len - length rest8"
				                   using q dec7_td by simp
				                 have rest3_le_patch: "length rest3 \<le> unat patch_len"
				                 proof -
				                   have "length rest3 = length (drop (unat (pr_t_C.pos_C vaaaa)) ?bs_td)"
				                     using drop_rest3 by simp
				                   also have "\<dots> \<le> length ?bs_td"
				                     by simp
				                   finally show ?thesis by simp
				                 qed
				                 have order: "pr_t_C.pos_C vaaaa \<le> pr_t_C.pos_C vabaa"
				                 proof -
				                   have "unat (pr_t_C.pos_C vaaaa) \<le> unat (pr_t_C.pos_C vabaa)"
				                     using pos_vaaaa pos_vabaa rest8_le_rest3 rest3_le_patch by arith
				                   thus ?thesis by (simp add: word_le_nat_alt)
				                 qed
		                 have diff_unat:
		                   "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa) =
		                    length rest3 - length rest8"
		                 proof -
		                   have "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa) =
		                         unat (pr_t_C.pos_C vabaa) - unat (pr_t_C.pos_C vaaaa)"
		                     using order by (simp add: unat_sub word_le_nat_alt)
			                   also have "\<dots> = length rest3 - length rest8"
			                     using pos_vaaaa pos_vabaa rest8_le_rest3 rest3_le_patch by arith
		                   finally show ?thesis .
		                 qed
		                 have "length rest3 - length rest8 \<le> unat (val_C vaaaa)"
		                   using dlen_exact dlen_val by arith
			                 hence "\<not> val_C vaaaa < pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa"
			                   using diff_unat by (simp add: word_less_nat_alt)
			                 thus ?thesis using q by simp
			               qed
			               subgoal premises q for vab vaba vabaa
			               proof -
			                 have pos_vaaaa:
			                   "unat (pr_t_C.pos_C vaaaa) = unat patch_len - length rest3"
			                   using prems dec3 by simp
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 have pos_vaba:
			                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
			                   using q dec6_td by simp
			                 have drop_rest7:
			                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
			                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
			                 have dec7_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
			                    Some (addr_len, rest8)"
			                   using dec7 drop_rest7 by simp
				                 have pos_vabaa:
				                   "unat (pr_t_C.pos_C vabaa) = unat patch_len - length rest8"
				                   using q dec7_td by simp
				                 have rest3_le_patch: "length rest3 \<le> unat patch_len"
				                 proof -
				                   have "length rest3 = length (drop (unat (pr_t_C.pos_C vaaaa)) ?bs_td)"
				                     using drop_rest3 by simp
				                   also have "\<dots> \<le> length ?bs_td"
				                     by simp
				                   finally show ?thesis by simp
				                 qed
				                 have data_val: "unat (val_C vab) = data_len"
				                   using q dec5_td by simp
			                 have inst_val: "unat (val_C vaba) = inst_len"
			                   using q dec6_td by simp
			                 have addr_val: "unat (val_C vabaa) = addr_len"
			                   using q dec7_td by simp
				                 have order: "pr_t_C.pos_C vaaaa \<le> pr_t_C.pos_C vabaa"
				                 proof -
				                   have "unat (pr_t_C.pos_C vaaaa) \<le> unat (pr_t_C.pos_C vabaa)"
				                     using pos_vaaaa pos_vabaa rest8_le_rest3 rest3_le_patch by arith
				                   thus ?thesis by (simp add: word_le_nat_alt)
				                 qed
			                 have diff_unat:
			                   "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa) =
			                    length rest3 - length rest8"
			                 proof -
			                   have "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa) =
			                         unat (pr_t_C.pos_C vabaa) - unat (pr_t_C.pos_C vaaaa)"
			                     using order by (simp add: unat_sub word_le_nat_alt)
			                   also have "\<dots> = length rest3 - length rest8"
			                     using pos_vaaaa pos_vabaa rest8_le_rest3 rest3_le_patch by arith
			                   finally show ?thesis .
			                 qed
			                 let ?alen_w =
			                   "((if UCAST(8 \<rightarrow> 32)
			                         (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			                       (4 :: 32 word) \<noteq> 0
			                      then 4 else 0) :: 32 word)"
			                 have alen_unat: "unat ?alen_w = alen"
			                   using alen_eq
			                   by (cases "UCAST(8 \<rightarrow> 32)
			                        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			                       (4 :: 32 word) \<noteq> 0")
			                      (simp_all add: unat_of_nat)
				                 have patch_lt: "unat patch_len < 4294967296"
			                   using unat_lt2p[of patch_len] by simp
			                 have total_lt0:
			                   "alen + data_len + inst_len + addr_len < 4294967296"
			                   using sizes_ok rest8_le_rest3 rest3_le_patch patch_lt by arith
			                 hence total_lt:
			                   "data_len + inst_len + addr_len + alen < 4294967296"
			                   by arith
			                 have data_inst_lt: "data_len + inst_len < 4294967296"
			                   using total_lt by arith
			                 have rhs1:
			                   "unat (val_C vab + val_C vaba) = data_len + inst_len"
			                   using data_val inst_val data_inst_lt
			                   by (simp add: unat_add_lem[THEN iffD1])
			                 have data_inst_addr_lt:
			                   "data_len + inst_len + addr_len < 4294967296"
			                   using total_lt by arith
			                 have rhs2:
			                   "unat (val_C vab + val_C vaba + val_C vabaa) =
			                    data_len + inst_len + addr_len"
			                   using rhs1 addr_val data_inst_addr_lt
			                   by (simp add: unat_add_lem[THEN iffD1])
			                 have rhs_unat:
			                   "unat (val_C vab + val_C vaba + val_C vabaa + ?alen_w) =
			                    data_len + inst_len + addr_len + alen"
			                   using rhs2 alen_unat total_lt
			                   by (simp add: unat_add_lem[THEN iffD1])
			                 have delta_le:
			                   "pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa \<le> val_C vaaaa"
			                 proof -
			                   have "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa) \<le>
			                         unat (val_C vaaaa)"
			                     using diff_unat dlen_exact dlen_val by arith
			                   thus ?thesis by (simp add: word_le_nat_alt)
			                 qed
			                 have lhs_unat:
			                   "unat (val_C vaaaa -
			                      (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa)) =
			                    alen + data_len + inst_len + addr_len"
			                 proof -
			                   have "unat (val_C vaaaa -
			                          (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa)) =
			                         unat (val_C vaaaa) -
			                         unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa)"
			                     using delta_le by (simp add: unat_sub word_le_nat_alt)
			                   also have "\<dots> = alen + data_len + inst_len + addr_len"
			                     using dlen_exact dlen_val diff_unat by arith
			                   finally show ?thesis .
			                 qed
			                 have size_eq:
			                   "val_C vaaaa - (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa) =
			                    val_C vab + val_C vaba + val_C vabaa + ?alen_w"
			                 proof -
			                   have "unat (val_C vaaaa -
			                          (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaaaa)) =
			                         unat (val_C vab + val_C vaba + val_C vabaa + ?alen_w)"
			                     using lhs_unat rhs_unat by arith
			                   thus ?thesis by (rule word_unat.Rep_inject[THEN iffD1])
			                 qed
			                 thus ?thesis using q by simp
			               qed
				               sorry \<comment> \<open>source outer decode loop body-preservation residual\<close>
				           qed
		           subgoal by (rule word_plus_one_le_of_less; simp)
		           subgoal premises prems for vaa
		           proof -
		             have some:
		               "\<exists>nv rest.
		                  varint_decode
		                    (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
		               using app_no_source_prefix_decodes[where td=td and va=va] prems by blast
		             then obtain nv rest' where dec:
		               "varint_decode
		                  (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
		               by blast
		             have "pr_t_C.err_C vaa = 0"
		               using prems dec by simp
		             with prems show ?thesis by simp
		           qed
		           subgoal premises prems for vaa
		           proof -
		             have some:
		               "\<exists>nv rest.
		                  varint_decode
		                    (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
		               using app_no_source_prefix_decodes[where td=td and va=va] prems by blast
		             then obtain nv rest' where dec:
		               "varint_decode
		                  (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
		               by blast
		             have "pr_t_C.err_C vaa = 0"
		               using prems dec by simp
		             with prems show ?thesis by simp
		           qed
		           subgoal premises prems for vaa
		           proof -
		             have some:
		               "\<exists>nv rest.
		                  varint_decode
		                    (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
		               using app_no_source_prefix_decodes[where td=td and va=va] prems by blast
		             then obtain nv rest' where dec:
		               "varint_decode
		                  (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
		               by blast
		             have "pr_t_C.err_C vaa = 0"
		               using prems dec by simp
		             with prems show ?thesis by simp
		           qed
		           subgoal premises prems for vaa
		           proof -
		             obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
		               dec3:
		                 "varint_decode
		                    (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                      (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3)"
		               and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
		               and di0: "pop_byte rest4 = Some (0, rest5)"
		               and dec5: "varint_decode rest5 = Some (data_len, rest6)"
		               and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
		               and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
		               and sizes_ok:
		                 "alen + data_len + inst_len + addr_len \<le> length rest8"
		               and dlen_exact:
		                 "dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len"
		               using app_no_source_prefix_decodes[where td=td and va=va] prems by blast
		             have rest8_le_rest3: "length rest8 \<le> length rest3"
		             proof -
		               have "length rest4 \<le> length rest3"
		                 by (rule varint_decode_length[OF dec4])
		               moreover have "length rest5 < length rest4"
		               proof -
		                 obtain b bs where rest4_eq: "rest4 = b # bs"
		                   using di0 by (cases rest4) (auto simp: pop_byte_def)
		                 moreover have "rest5 = bs"
		                   using di0 rest4_eq by (simp add: pop_byte_def)
		                 ultimately show ?thesis by simp
		               qed
		               moreover have "length rest6 \<le> length rest5"
		                 by (rule varint_decode_length[OF dec5])
		               moreover have "length rest7 \<le> length rest6"
		                 by (rule varint_decode_length[OF dec6])
		               moreover have "length rest8 \<le> length rest7"
		                 by (rule varint_decode_length[OF dec7])
		               ultimately show ?thesis by arith
		             qed
		             have dlen_le: "dlen \<le> length rest3"
		               using sizes_ok dlen_exact rest8_le_rest3 by arith
		             have val_eq: "unat (val_C vaa) = dlen"
		               using prems dec3 by simp
		             have pos_eq: "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest3"
		               using prems dec3 by simp
		             have rem_eq:
		               "unat (patch_len - pr_t_C.pos_C vaa) = length rest3"
		             proof -
		               have "unat (patch_len - pr_t_C.pos_C vaa) =
		                     unat patch_len - unat (pr_t_C.pos_C vaa)"
		                 using prems by (simp add: unat_sub word_le_nat_alt)
		               also have "\<dots> = length rest3"
		               proof -
		                 have "length rest3 \<le> unat patch_len"
		                 proof -
		                   have "length rest3 \<le>
		                         length (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                           (heap_bytes td patch (unat patch_len)))"
		                     by (rule varint_decode_length[OF dec3])
		                   thus ?thesis by simp
		                 qed
		                 with pos_eq show ?thesis by arith
		               qed
		               finally show ?thesis .
		             qed
		             have "val_C vaa \<le> patch_len - pr_t_C.pos_C vaa"
		               using dlen_le val_eq rem_eq by (simp add: word_le_nat_alt)
		             with prems show False
		               by (simp add: word_le_not_less)
		           qed
		           subgoal premises prems for vaa vaaa
		           proof -
		             have some:
		               "\<exists>nv rest.
		                  varint_decode
		                    (drop (unat (pr_t_C.pos_C vaa))
		                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
		               apply (rule app_no_source_tgt_decode_some)
		               using prems apply simp_all
		               done
		             then obtain nv rest' where dec:
		               "varint_decode
		                  (drop (unat (pr_t_C.pos_C vaa))
		                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
		               by blast
		             have "pr_t_C.err_C vaaa = 0"
		               using prems dec by simp
		             with prems show ?thesis by simp
		           qed
		           subgoal premises prems for vaa vaaa
		           proof -
		             have some:
		               "\<exists>nv rest.
		                  varint_decode
		                    (drop (unat (pr_t_C.pos_C vaa))
		                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
		               apply (rule app_no_source_tgt_decode_some)
		               using prems apply simp_all
		               done
		             then obtain nv rest' where dec:
		               "varint_decode
		                  (drop (unat (pr_t_C.pos_C vaa))
		                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
		               by blast
		             have "pr_t_C.err_C vaaa = 0"
		               using prems dec by simp
		             with prems show ?thesis by simp
		           qed
		           subgoal premises prems for vaa vaaa
		           proof -
		             have some:
		               "\<exists>nv rest.
		                  varint_decode
		                    (drop (unat (pr_t_C.pos_C vaa))
		                      (heap_bytes td patch (unat patch_len))) = Some (nv, rest)"
		               apply (rule app_no_source_tgt_decode_some)
		               using prems apply simp_all
		               done
		             then obtain nv rest' where dec:
		               "varint_decode
		                  (drop (unat (pr_t_C.pos_C vaa))
		                    (heap_bytes td patch (unat patch_len))) = Some (nv, rest')"
		               by blast
		             have "pr_t_C.err_C vaaa = 0"
		               using prems dec by simp
		             with prems show ?thesis by simp
		           qed
		           subgoal premises prems for vaa vaaa
		           proof -
		             obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
		               dec3:
		                 "varint_decode
		                    (drop (unat (pr_t_C.pos_C va + val_C va + 1))
		                      (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3)"
		               and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
		               using app_no_source_prefix_decodes[where td=td and va=va] prems by blast
		             have pos_vaa:
		               "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest3"
		               using prems dec3 by simp
		             have drop_rest3:
		               "drop (unat (pr_t_C.pos_C vaa))
		                 (heap_bytes td patch (unat patch_len)) = rest3"
		               using varint_decode_drop_rest[OF dec3] pos_vaa by simp
		             have dec4_td:
		               "varint_decode
		                  (drop (unat (pr_t_C.pos_C vaa))
		                    (heap_bytes td patch (unat patch_len))) =
		                Some (pw_tgt_len win, rest4)"
		               using dec4 drop_rest3 by simp
		             have tgt_val: "unat (val_C vaaa) = pw_tgt_len win"
		               using prems dec4_td by simp
		             have "length tgt \<le> unat out_cap"
		               using out_cap_enough Inl by simp
		             hence "unat (val_C vaaa) \<le> unat out_cap"
		               using tgt_val tgt_len_eq by simp
		             hence "val_C vaaa \<le> out_cap"
		               by (simp add: word_le_nat_alt)
			             with prems show False
			               by simp
			           qed
			           subgoal premises prems for vaa vaaa
			           proof -
			             obtain rest3 rest4 rest5 rest6 rest7 rest8 dlen data_len inst_len addr_len alen where
			               dec3:
			                 "varint_decode
			                    (drop (unat (pr_t_C.pos_C va + val_C va + 1))
			                      (heap_bytes td patch (unat patch_len))) = Some (dlen, rest3)"
			               and dec4: "varint_decode rest3 = Some (pw_tgt_len win, rest4)"
			               and di0: "pop_byte rest4 = Some (0, rest5)"
			               and dec5: "varint_decode rest5 = Some (data_len, rest6)"
			               and dec6: "varint_decode rest6 = Some (inst_len, rest7)"
			               and dec7: "varint_decode rest7 = Some (addr_len, rest8)"
			               and sizes_ok:
			                 "alen + data_len + inst_len + addr_len \<le> length rest8"
			               and dlen_exact:
			                 "dlen = (length rest3 - length rest8) + alen + data_len + inst_len + addr_len"
			               and alen_eq:
			                 "alen =
			                   (if UCAST(8 \<rightarrow> 32)
			                         (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			                       (4 :: 32 word) \<noteq> 0
			                    then 4 else 0)"
			               using app_no_source_prefix_decodes[where td=td and va=va] prems by blast
			             have pos_vaa:
			               "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest3"
			               using prems dec3 by simp
			             have drop_rest3:
			               "drop (unat (pr_t_C.pos_C vaa))
			                 (heap_bytes td patch (unat patch_len)) = rest3"
			               using varint_decode_drop_rest[OF dec3] pos_vaa by simp
			             have dec4_td:
			               "varint_decode
			                 (drop (unat (pr_t_C.pos_C vaa))
			                   (heap_bytes td patch (unat patch_len))) =
			                Some (pw_tgt_len win, rest4)"
			               using dec4 drop_rest3 by simp
			             have pos_vaaa:
			               "unat (pr_t_C.pos_C vaaa) = unat patch_len - length rest4"
			               using prems dec4_td by simp
			             have drop_rest4:
			               "drop (unat (pr_t_C.pos_C vaaa))
			                 (heap_bytes td patch (unat patch_len)) = rest4"
			               using varint_decode_drop_rest[OF dec4_td] pos_vaaa by simp
			             have dlen_val: "unat (val_C vaa) = dlen"
			               using prems dec3 by simp
			             have rest4_cons: "rest4 = 0 # rest5"
			               using di0 by (cases rest4) (simp_all add: pop_byte_def)
			             let ?di_pos = "pr_t_C.pos_C vaaa"
			             let ?bs_td = "heap_bytes td patch (unat patch_len)"
			             have di_pos_lt_nat: "unat ?di_pos < unat patch_len"
			             proof -
			               have "drop (unat ?di_pos) ?bs_td \<noteq> []"
			                 using drop_rest4 rest4_cons by simp
			               thus ?thesis by (simp add: drop_eq_Nil)
			             qed
			             have di_pos_lt: "?di_pos < patch_len"
			               using di_pos_lt_nat by (simp add: word_less_nat_alt)
			             have heap_di0:
			               "heap_w8 td (patch +\<^sub>p uint ?di_pos) = 0"
			             proof -
			               have "?bs_td ! unat ?di_pos = 0"
			               proof -
			                 have "?bs_td ! unat ?di_pos =
			                       drop (unat ?di_pos) ?bs_td ! 0"
			                   using di_pos_lt_nat by (simp add: nth_drop)
			                 also have "\<dots> = 0"
			                   using drop_rest4 rest4_cons by simp
			                 finally show ?thesis .
			               qed
			               thus ?thesis
			                 using di_pos_lt_nat by (simp add: heap_bytes_nth)
			             qed
			             have ptr_di:
			               "ptr_valid (heap_typing td) (patch +\<^sub>p uint ?di_pos)"
			               using prems di_pos_lt_nat
			               by (auto simp: buf_valid_def)
			             have read_di:
			               "read_byte' patch patch_len ?di_pos td =
			                Some (pr_t_C (?di_pos + 1) 0 VCD_OK)"
			             proof -
			               have ptr_imp:
			                 "?di_pos < patch_len \<longrightarrow>
			                  ptr_valid (heap_typing td) (patch +\<^sub>p uint ?di_pos)"
			                 using ptr_di by simp
			               show ?thesis
			                 using read_byte'_spec[OF ptr_imp] di_pos_lt heap_di0 by simp
			             qed
			             have di_pos_suc:
			               "unat (?di_pos + 1) = Suc (unat ?di_pos)"
			               using unat_x_plus_1[OF di_pos_lt] by simp
			             have drop_rest5:
			               "drop (unat (?di_pos + 1)) ?bs_td = rest5"
			             proof -
			               have "drop (Suc (unat ?di_pos)) ?bs_td =
			                     tl (drop (unat ?di_pos) ?bs_td)"
			                 by (simp add: drop_Suc tl_drop)
			               also have "\<dots> = rest5"
			                 using drop_rest4 rest4_cons by simp
			               finally show ?thesis
			                 using di_pos_suc by simp
			             qed
			             have dec5_td:
			               "varint_decode (drop (unat (?di_pos + 1)) ?bs_td) =
			                Some (data_len, rest6)"
			               using dec5 drop_rest5 by simp
			             have rest8_le_rest3: "length rest8 \<le> length rest3"
			             proof -
			               have "length rest4 \<le> length rest3"
			                 by (rule varint_decode_length[OF dec4])
			               moreover have "length rest5 < length rest4"
			               proof -
			                 have "rest4 \<noteq> []"
			                   using rest4_cons by simp
			                 then show ?thesis using rest4_cons by simp
			               qed
			               moreover have "length rest6 \<le> length rest5"
			                 by (rule varint_decode_length[OF dec5])
			               moreover have "length rest7 \<le> length rest6"
			                 by (rule varint_decode_length[OF dec6])
			               moreover have "length rest8 \<le> length rest7"
			                 by (rule varint_decode_length[OF dec7])
			               ultimately show ?thesis by arith
			             qed
			             show ?thesis
			               apply (rule exI[where x = "pr_t_C (?di_pos + 1) 0 VCD_OK"])
			               apply (intro conjI)
			                apply (rule read_di)
			               apply simp
			               apply runs_to_vcg
			               subgoal using prems by simp
			               subgoal using di_pos_lt by (rule word_plus_one_le_of_less)
			               subgoal using dec5_td by simp
			               subgoal using dec5_td by simp
			               subgoal using dec5_td by simp
			               subgoal using prems by simp
			               subgoal premises q for vab vaba
			               proof -
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 show ?thesis using q dec6_td by simp
			               qed
			               subgoal premises q for vab vaba
			               proof -
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 show ?thesis using q dec6_td by simp
			               qed
			               subgoal premises q for vab vaba
			               proof -
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 show ?thesis using q dec6_td by simp
			               qed
			               subgoal using prems by simp
			               subgoal premises q for vab vaba vabaa
			               proof -
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 have pos_vaba:
			                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
			                   using q dec6_td by simp
			                 have drop_rest7:
			                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
			                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
			                 have dec7_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
			                    Some (addr_len, rest8)"
			                   using dec7 drop_rest7 by simp
			                 show ?thesis using q dec7_td by simp
			               qed
			               subgoal premises q for vab vaba vabaa
			               proof -
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 have pos_vaba:
			                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
			                   using q dec6_td by simp
			                 have drop_rest7:
			                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
			                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
			                 have dec7_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
			                    Some (addr_len, rest8)"
			                   using dec7 drop_rest7 by simp
			                 show ?thesis using q dec7_td by simp
			               qed
			               subgoal premises q for vab vaba vabaa
			               proof -
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 have pos_vaba:
			                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
			                   using q dec6_td by simp
			                 have drop_rest7:
			                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
			                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
			                 have dec7_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
			                    Some (addr_len, rest8)"
			                   using dec7 drop_rest7 by simp
			                 show ?thesis using q dec7_td by simp
			               qed
			               subgoal premises q for vab vaba vabaa
			               proof -
			                 have pos_vaa:
			                   "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest3"
			                   using prems dec3 by simp
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 have pos_vaba:
			                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
			                   using q dec6_td by simp
			                 have drop_rest7:
			                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
			                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
			                 have dec7_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
			                    Some (addr_len, rest8)"
			                   using dec7 drop_rest7 by simp
			                 have pos_vabaa:
			                   "unat (pr_t_C.pos_C vabaa) = unat patch_len - length rest8"
			                   using q dec7_td by simp
			                 have rest3_le_patch: "length rest3 \<le> unat patch_len"
			                 proof -
			                   have "length rest3 = length (drop (unat (pr_t_C.pos_C vaa)) ?bs_td)"
			                     using drop_rest3 by simp
			                   also have "\<dots> \<le> length ?bs_td"
			                     by simp
			                   finally show ?thesis by simp
			                 qed
			                 have order: "pr_t_C.pos_C vaa \<le> pr_t_C.pos_C vabaa"
			                 proof -
			                   have "unat (pr_t_C.pos_C vaa) \<le> unat (pr_t_C.pos_C vabaa)"
			                     using pos_vaa pos_vabaa rest8_le_rest3 rest3_le_patch by arith
			                   thus ?thesis by (simp add: word_le_nat_alt)
			                 qed
			                 have diff_unat:
			                   "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa) =
			                    length rest3 - length rest8"
			                 proof -
			                   have "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa) =
			                         unat (pr_t_C.pos_C vabaa) - unat (pr_t_C.pos_C vaa)"
			                     using order by (simp add: unat_sub word_le_nat_alt)
			                   also have "\<dots> = length rest3 - length rest8"
			                     using pos_vaa pos_vabaa rest8_le_rest3 rest3_le_patch by arith
			                   finally show ?thesis .
			                 qed
			                 have "length rest3 - length rest8 \<le> unat (val_C vaa)"
			                   using dlen_exact dlen_val by arith
			                 hence "\<not> val_C vaa < pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa"
			                   using diff_unat by (simp add: word_less_nat_alt)
			                 thus ?thesis using q by simp
			               qed
			               subgoal premises q for vab vaba vabaa
			               proof -
			                 have pos_vaa:
			                   "unat (pr_t_C.pos_C vaa) = unat patch_len - length rest3"
			                   using prems dec3 by simp
			                 have pos_vab:
			                   "unat (pr_t_C.pos_C vab) = unat patch_len - length rest6"
			                   using q dec5_td by simp
			                 have drop_rest6:
			                   "drop (unat (pr_t_C.pos_C vab)) ?bs_td = rest6"
			                   using varint_decode_drop_rest[OF dec5_td] pos_vab by simp
			                 have dec6_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vab)) ?bs_td) =
			                    Some (inst_len, rest7)"
			                   using dec6 drop_rest6 by simp
			                 have pos_vaba:
			                   "unat (pr_t_C.pos_C vaba) = unat patch_len - length rest7"
			                   using q dec6_td by simp
			                 have drop_rest7:
			                   "drop (unat (pr_t_C.pos_C vaba)) ?bs_td = rest7"
			                   using varint_decode_drop_rest[OF dec6_td] pos_vaba by simp
			                 have dec7_td:
			                   "varint_decode (drop (unat (pr_t_C.pos_C vaba)) ?bs_td) =
			                    Some (addr_len, rest8)"
			                   using dec7 drop_rest7 by simp
			                 have pos_vabaa:
			                   "unat (pr_t_C.pos_C vabaa) = unat patch_len - length rest8"
			                   using q dec7_td by simp
			                 have rest3_le_patch: "length rest3 \<le> unat patch_len"
			                 proof -
			                   have "length rest3 = length (drop (unat (pr_t_C.pos_C vaa)) ?bs_td)"
			                     using drop_rest3 by simp
			                   also have "\<dots> \<le> length ?bs_td"
			                     by simp
			                   finally show ?thesis by simp
			                 qed
			                 have data_val: "unat (val_C vab) = data_len"
			                   using q dec5_td by simp
			                 have inst_val: "unat (val_C vaba) = inst_len"
			                   using q dec6_td by simp
			                 have addr_val: "unat (val_C vabaa) = addr_len"
			                   using q dec7_td by simp
			                 have order: "pr_t_C.pos_C vaa \<le> pr_t_C.pos_C vabaa"
			                 proof -
			                   have "unat (pr_t_C.pos_C vaa) \<le> unat (pr_t_C.pos_C vabaa)"
			                     using pos_vaa pos_vabaa rest8_le_rest3 rest3_le_patch by arith
			                   thus ?thesis by (simp add: word_le_nat_alt)
			                 qed
			                 have diff_unat:
			                   "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa) =
			                    length rest3 - length rest8"
			                 proof -
			                   have "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa) =
			                         unat (pr_t_C.pos_C vabaa) - unat (pr_t_C.pos_C vaa)"
			                     using order by (simp add: unat_sub word_le_nat_alt)
			                   also have "\<dots> = length rest3 - length rest8"
			                     using pos_vaa pos_vabaa rest8_le_rest3 rest3_le_patch by arith
			                   finally show ?thesis .
			                 qed
			                 let ?alen_w =
			                   "((if UCAST(8 \<rightarrow> 32)
			                         (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			                       (4 :: 32 word) \<noteq> 0
			                      then 4 else 0) :: 32 word)"
			                 have alen_unat: "unat ?alen_w = alen"
			                   using alen_eq
			                   by (cases "UCAST(8 \<rightarrow> 32)
			                        (heap_w8 td (patch +\<^sub>p uint (pr_t_C.pos_C va + val_C va))) AND
			                       (4 :: 32 word) \<noteq> 0")
			                      (simp_all add: unat_of_nat)
			                 have patch_lt: "unat patch_len < 4294967296"
			                   using unat_lt2p[of patch_len] by simp
			                 have total_lt0:
			                   "alen + data_len + inst_len + addr_len < 4294967296"
			                   using sizes_ok rest8_le_rest3 rest3_le_patch patch_lt by arith
			                 hence total_lt:
			                   "data_len + inst_len + addr_len + alen < 4294967296"
			                   by arith
			                 have data_inst_lt: "data_len + inst_len < 4294967296"
			                   using total_lt by arith
			                 have rhs1:
			                   "unat (val_C vab + val_C vaba) = data_len + inst_len"
			                   using data_val inst_val data_inst_lt
			                   by (simp add: unat_add_lem[THEN iffD1])
			                 have data_inst_addr_lt:
			                   "data_len + inst_len + addr_len < 4294967296"
			                   using total_lt by arith
			                 have rhs2:
			                   "unat (val_C vab + val_C vaba + val_C vabaa) =
			                    data_len + inst_len + addr_len"
			                   using rhs1 addr_val data_inst_addr_lt
			                   by (simp add: unat_add_lem[THEN iffD1])
			                 have rhs_unat:
			                   "unat (val_C vab + val_C vaba + val_C vabaa + ?alen_w) =
			                    data_len + inst_len + addr_len + alen"
			                   using rhs2 alen_unat total_lt
			                   by (simp add: unat_add_lem[THEN iffD1])
			                 have delta_le:
			                   "pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa \<le> val_C vaa"
			                 proof -
			                   have "unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa) \<le>
			                         unat (val_C vaa)"
			                     using diff_unat dlen_exact dlen_val by arith
			                   thus ?thesis by (simp add: word_le_nat_alt)
			                 qed
			                 have lhs_unat:
			                   "unat (val_C vaa -
			                      (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa)) =
			                    alen + data_len + inst_len + addr_len"
			                 proof -
			                   have "unat (val_C vaa -
			                          (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa)) =
			                         unat (val_C vaa) -
			                         unat (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa)"
			                     using delta_le by (simp add: unat_sub word_le_nat_alt)
			                   also have "\<dots> = alen + data_len + inst_len + addr_len"
			                     using dlen_exact dlen_val diff_unat by arith
			                   finally show ?thesis .
			                 qed
			                 have size_eq:
			                   "val_C vaa - (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa) =
			                    val_C vab + val_C vaba + val_C vabaa + ?alen_w"
			                 proof -
			                   have "unat (val_C vaa -
			                          (pr_t_C.pos_C vabaa - pr_t_C.pos_C vaa)) =
			                         unat (val_C vab + val_C vaba + val_C vabaa + ?alen_w)"
			                     using lhs_unat rhs_unat by arith
			                   thus ?thesis by (rule word_unat.Rep_inject[THEN iffD1])
			                 qed
			                 thus ?thesis using q by simp
			               qed
				               sorry \<comment> \<open>no-source outer decode loop body-preservation residual\<close>
				           qed
						           done
				         subgoal sorry \<comment> \<open>truncation branch — contradiction from Inl, deferred\<close>
         done
      \<comment> \<open>Remaining 3 main-body subgoals (code_tbl=0 × has-src,
          code_tbl≠0 × has-src ∈ {0,1}).\<close>
      sorry
  qed
  thus ?thesis by (simp add: Inl)
next
  case (Inr e)
  \<comment> \<open>Completeness on rejection: if the spec rejects the input, the C
      decoder returns a nonzero error code.  Strategy: run the full
      supply-runs_to_vcg and let the residual subgoals identify the
      specific failure path in C corresponding to each spec failure.\<close>
  let ?Post = "\<lambda>r t. \<exists>e. r = Result (e :: int) \<and> e \<noteq> 0"
  have "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s \<lbrace> ?Post \<rbrace>"
    sorry
  thus ?thesis by (simp add: Inr)
qed

end

end
