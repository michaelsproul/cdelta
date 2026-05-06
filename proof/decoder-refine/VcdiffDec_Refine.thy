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
