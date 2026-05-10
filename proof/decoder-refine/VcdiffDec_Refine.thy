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
(* ---------- vcdiff_decode main refinement (TODO) ---------- *)

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
      and dlen_ok: "varint_decode wbs1 = Some (dlen, wbs2)"
      and tgt_ok: "varint_decode wbs2 = Some (tgt_len, wbs3)"
      and di_pop: "pop_byte wbs3 = Some (di, wbs4)"
      and di_zero: "di = 0"
      and data_ok: "varint_decode wbs4 = Some (data_len, wbs5)"
      and inst_ok: "varint_decode wbs5 = Some (inst_len, wbs6)"
      and addr_ok: "varint_decode wbs6 = Some (addr_len, wbs7)"
      and sizes_ok: "data_len + inst_len + addr_len \<le> length wbs7"
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
        data_ok inst_ok addr_ok sizes_ok
  by (simp add: pop_byte_def Let_def add.commute add.left_commute
           split: list.splits option.splits)

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
            dlen_ok tgt_ok di_pop di_zero data_ok inst_ok addr_ok sizes_ok])
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
          \<and> heap_typing t = heap_typing s0 \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 4 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 4
              \<and> heap_bytes st buf n = heap_bytes s0 buf n
              \<and> buf_valid st buf n = buf_valid s0 buf n
              \<and> heap_w32 st p = heap_w32 s0 p
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
          \<and> heap_typing t = heap_typing s0 \<rbrace>"
  apply (rule runs_to_whileLoop_res'[
     where R = "measure (\<lambda>((idx :: 32 word), _). 768 - unat idx)"
       and I = "\<lambda>idx st. unat idx \<le> 768
              \<and> heap_bytes st buf n = heap_bytes s0 buf n
              \<and> buf_valid st buf n = buf_valid s0 buf n
              \<and> heap_w32 st p = heap_w32 s0 p
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

lemma runs_to_whileLoop_bind_drop6th:
  assumes wl: "whileLoop C B a \<bullet> s
    \<lbrace>\<lambda>r t. case r of
       Exn e \<Rightarrow> Q (Exn e) t
     | Result v \<Rightarrow> Q (Result (fst v, fst (snd v), fst (snd (snd v)),
                              fst (snd (snd (snd v))), fst (snd (snd (snd (snd v)))))) t\<rbrace>"
  shows "(whileLoop C B a >>= (\<lambda>v. return (fst v, fst (snd v), fst (snd (snd v)),
                                            fst (snd (snd (snd v))), fst (snd (snd (snd (snd v)))))))
         \<bullet> s \<lbrace>Q\<rbrace>"
  apply (rule runs_to_bind_exception[where f = "whileLoop C B a"])
  apply (rule runs_to_weaken[OF wl])
  apply (auto simp: Exn_def default_option_def split: exception_or_result_splits)
  done

lemma runs_to_whileLoop_bind_drop6th':
  assumes wl: "whileLoop C B a \<bullet> s
    \<lbrace>\<lambda>r t. case r of
       Exn e \<Rightarrow> Q (Exn e) t
     | Result v \<Rightarrow> Q (Result (fst v, fst (snd v), fst (snd (snd v)),
                              fst (snd (snd (snd v))), fst (snd (snd (snd (snd v)))))) t\<rbrace>"
  shows "(whileLoop C B a >>= (\<lambda>(a, b, c, d, e, f). return (a, b, c, d, e)))
         \<bullet> s \<lbrace>Q\<rbrace>"
proof -
  have eq: "(\<lambda>(a, b, c, d, e, f). return (a, b, c, d, e))
          = (\<lambda>v. return (fst v, fst (snd v), fst (snd (snd v)),
                         fst (snd (snd (snd v))), fst (snd (snd (snd (snd v))))))"
    by (auto simp: case_prod_beta)
  show ?thesis unfolding eq by (rule runs_to_whileLoop_bind_drop6th[OF wl])
qed

lemma summand_le_from_sub_eq:
  fixes v gap a b c :: "32 word"
  assumes eq: "v - gap = a + b + c"
    and no_under: "\<not> unat v < unat gap"
    and no_over: "unat a + unat b + unat c \<le> unat v"
  shows "c \<le> v"
proof -
  have "unat c \<le> unat a + unat b + unat c" by simp
  also have "\<dots> \<le> unat v" by (rule no_over)
  finally show ?thesis by (simp add: word_le_nat_alt)
qed

lemma inst_end_from_sizes:
  fixes pos_v pos_vd val_v val_vb val_vc val_vd patch_len :: "32 word"
  assumes eq: "val_v - (pos_vd - pos_v) = val_vb + val_vc + val_vd"
    and bound1: "\<not> unat (patch_len - pos_v) < unat val_v"
    and pv_le: "pos_v \<le> patch_len"
    and vd_le_v: "val_vd \<le> val_v"
  shows "unat (pos_vd + val_vb + val_vc) \<le> unat patch_len"
  using inst_end_le_patch_len[OF eq bound1 pv_le vd_le_v]
  by (simp add: word_le_nat_alt)

lemma inst_end_from_sizes':
  fixes pos_v pos_vd val_v val_vb val_vc val_vd patch_len :: "32 word"
  assumes "val_v - (pos_vd - pos_v) = val_vb + val_vc + val_vd"
    and "\<not> unat (patch_len - pos_v) < unat val_v"
    and "pos_v \<le> patch_len"
    and "val_vd \<le> val_v"
  shows "unat (pos_vd + val_vb + val_vc) \<le> unat patch_len"
  by (rule inst_end_from_sizes[OF assms])


lemma vcdiff_decode'_prefix_correct:
  fixes patch :: "8 word ptr" and patch_len :: "32 word"
    and src :: "8 word ptr" and src_len :: "32 word"
    and out :: "8 word ptr" and out_cap :: "32 word"
    and out_len :: "32 word ptr"
    and bs :: "8 word list"
  assumes bs_def: "bs = heap_bytes s patch (unat patch_len)"
      and out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch (unat patch_len)"
      and code_tbl_ready: "code_tbl_built_'' s \<noteq> 0"
      and len_ge6: "6 \<le> unat patch_len"
      \<comment> \<open>Header magic and indicator\<close>
      and magic0: "heap_w8 s patch = 0xD6"
      and magic1: "heap_w8 s (patch +\<^sub>p 1) = 0xC3"
      and magic2: "heap_w8 s (patch +\<^sub>p 2) = 0xC4"
      and magic3: "heap_w8 s (patch +\<^sub>p 3) = 0x00"
      and hdr_ok: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 3 = 0"
      and no_app: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 4)) AND 4 = 0"
      \<comment> \<open>Window indicator at byte 5\<close>
      and win_no_target: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 2 = 0"
      and win_mask_ok: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 0xFFFFFFFA = 0"
      and win_no_source: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 1 = 0"
      and win_no_adler: "UCAST(8 \<rightarrow> 32) (heap_w8 s (patch +\<^sub>p 5)) AND 4 = 0"
      \<comment> \<open>Varint decodes on the buffer tail (starting at position 6)\<close>
      and dlen_ok: "varint_decode (drop 6 bs) = Some (dlen_n, rest_dlen)"
      and tgt_ok: "varint_decode rest_dlen = Some (tgt_n, rest_tgt)"
      \<comment> \<open>di byte = 0 at the position after tgt_len\<close>
      and rest_tgt_nonempty: "rest_tgt \<noteq> []"
      and di_zero: "hd rest_tgt = 0"
      \<comment> \<open>Remaining varints\<close>
      and data_ok: "varint_decode (tl rest_tgt) = Some (data_n, rest_data)"
      and inst_ok: "varint_decode rest_data = Some (inst_n, rest_inst)"
      and addr_ok: "varint_decode rest_inst = Some (addr_n, rest_addr)"
      \<comment> \<open>Section sizes fit within remaining buffer\<close>
      and sizes_ok: "data_n + inst_n + addr_n \<le> length rest_addr"
      \<comment> \<open>Target length fits in output buffer\<close>
      and tgt_fits: "of_nat tgt_n \<le> out_cap"
      \<comment> \<open>dlen consistency check (the C checks remaining = data+inst+addr+adler)\<close>
      and dlen_consistent: "dlen_n = (length (drop 6 bs) - length rest_addr)"
      \<comment> \<open>Output buffer validity and disjointness (needed for inner loop guards)\<close>
      and out_ok: "buf_valid s out (unat out_cap)"
      and out_patch_disj: "\<forall>i < unat out_cap. \<forall>j < unat patch_len.
           out +\<^sub>p int i \<noteq> patch +\<^sub>p int j"
      and out_inj: "\<forall>i < unat out_cap. \<forall>j < unat out_cap.
           i \<noteq> j \<longrightarrow> out +\<^sub>p int i \<noteq> out +\<^sub>p int j"
      and out_cap_bound: "unat out_cap < 2 ^ 32"
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t. \<exists>ret. r = Result ret \<rbrace>"
proof -
  have patch0_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 0)"
    using buf_validD[OF patch_ok, of 0] len_ge6 by simp
  have patch1_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 1)"
    using buf_validD[OF patch_ok, of 1] len_ge6 by simp
  have patch2_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 2)"
    using buf_validD[OF patch_ok, of 2] len_ge6 by simp
  have patch3_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 3)"
    using buf_validD[OF patch_ok, of 3] len_ge6 by simp
  have patch4_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 4)"
    using buf_validD[OF patch_ok, of 4] len_ge6 by simp
  have patch5_ok: "ptr_valid (heap_typing s) (patch +\<^sub>p int 5)"
    using buf_validD[OF patch_ok, of 5] len_ge6 by simp
  have len_ge5: "5 \<le> patch_len"
    using len_ge6 by (simp add: word_le_nat_alt)
  have magic0_uint: "uint (heap_w8 s patch) = 214"
    using magic0 by simp
  have magic1_uint: "uint (heap_w8 s (patch +\<^sub>p 1)) = 195"
    using magic1 by simp
  have magic2_uint: "uint (heap_w8 s (patch +\<^sub>p 2)) = 196"
    using magic2 by simp
  have magic3_uint: "uint (heap_w8 s (patch +\<^sub>p 3)) = 0"
    using magic3 by simp
  \<comment> \<open>The dlen varint decode starts at position 6 in the buffer\<close>
  have dlen_at_6: "varint_decode (drop (unat (6 :: 32 word)) (heap_bytes s patch (unat patch_len)))
                   = Some (dlen_n, rest_dlen)"
    using dlen_ok bs_def by simp
  have dlen_fits: "dlen_n < 2 ^ 32"
    by (rule varint_decode_value_bound[OF dlen_ok])
  have pos6_le: "(6 :: 32 word) \<le> patch_len"
    using len_ge6 by (simp add: word_le_nat_alt)
  have patch_ok': "buf_valid s patch (unat patch_len)" by (rule patch_ok)
  show ?thesis sorry
qed

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
  assumes out_len_ok: "ptr_valid (heap_typing s) out_len"
      and patch_ok: "buf_valid s patch (unat patch_len)"
      and src_ok:   "buf_valid s src   (unat src_len)"
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
  shows "vcdiff_decode' patch patch_len src src_len out out_cap out_len \<bullet> s
           \<lbrace> \<lambda>r t.
             case decode_spec (heap_bytes s patch (unat patch_len))
                              (heap_bytes s src   (unat src_len)) of
               Inl tgt \<Rightarrow> r = Result (0 :: int) \<and>
                          unat (heap_w32 t out_len) = length tgt \<and>
                          heap_bytes t out (length tgt) = tgt
             | Inr _   \<Rightarrow> (\<exists>e. r = Result (e :: int) \<and> e \<noteq> 0) \<rbrace>"
  sorry

end

end
