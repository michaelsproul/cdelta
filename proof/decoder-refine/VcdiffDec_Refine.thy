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

(* ---------- Buffer validity ---------- *)

definition buf_valid :: "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> nat \<Rightarrow> bool" where
  "buf_valid s buf n =
     (\<forall>i < n. ptr_valid (heap_typing s) (buf +\<^sub>p int i))"

lemma buf_validD:
  "\<lbrakk> buf_valid s buf n; i < n \<rbrakk> \<Longrightarrow> ptr_valid (heap_typing s) (buf +\<^sub>p int i)"
  by (simp add: buf_valid_def)

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
      done
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
          sorry
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

(* ---------- vcdiff_decode main refinement (TODO) ---------- *)

(*
  The big one. Top-level Hoare triple:

    {{ ptr_valid patch_len; ptr_valid src_len; ptr_valid out_cap;
       ptr_valid out_len; buffer preconds; disjoint_buffers;
       src_len, patch_len, out_cap < 2^32 }}
      vcdiff_decode' patch patch_len src src_len out out_cap out_len
    {{ λrv s'.
        case decode_spec (heap_bytes s patch (unat patch_len))
                         (heap_bytes s src (unat src_len)) of
          Inl tgt ⇒
            rv = Result VCD_OK \<and>
            heap_bytes s' out (length tgt) = tgt \<and>
            heap_w32 s' out_len = of_nat (length tgt) \<and>
            (pointers outside [out..length tgt), out_len, near_arr, same_arr
              unchanged)
        | Inr _ ⇒ rv ≠ Result VCD_OK }}

  Proof structure (top-down):
    1. Header parse (magic, 0x00, Hdr_Indicator): 30 lines, mechanical.
    2. Adler-32 skip and window header: another 30 lines, calls read_varint'.
    3. Main while loop over inst_cursor < inst_end.
    4. Cache re-init + code_tbl build precondition.
    5. Size-consistency post-checks (tgt_pos = tgt_len etc).

  The main loop invariant ties the C's (data_cursor, inst_cursor,
  addr_cursor, tgt_pos, near_ptr, near_arr, same_arr) to the spec's
  decode_loop state via encode_window_loop_decode_loop.

  Effort: ~2 weeks, dominated by the main-loop invariant.
*)

end

end
