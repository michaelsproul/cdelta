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
                           (case decoded of
                              Some (nv, rest) \<Rightarrow>
                                pr_t_C.err_C e = VCD_OK \<and>
                                unat (pr_t_C.pos_C e) = unat len - length rest \<and>
                                nv = unat (pr_t_C.val_C e)
                            | None \<Rightarrow> pr_t_C.err_C e \<noteq> VCD_OK))"
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
    \<comment> \<open>Exn post: Exn invariant already contains exactly what we need.\<close>
    by (clarsimp simp: Let_def split: prod.splits option.splits)
  subgoal
    \<comment> \<open>Body: 16 subgoals after runs_to_vcg. 10 are closable with existing
        tactics (bounds / IS_VALID / measure). The 6 substantive goals
        (truncation-throw post, overflow-throw post, success-throw post,
        and four continue-path invariant conjuncts) remain: they require
        varint_decode_loop stepping via varint_acc_step and
        varint_overflow_check_nat + list-drop chaining via
        heap_bytes_drop_shift.\<close>
    apply (clarsimp simp: Let_def split: prod.splits)
    apply runs_to_vcg
    oops

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

(* ---------- decode_address refinement (TODO) ---------- *)

(*
  Hoare-triple contract for decode_address'. Mirrors the pure
  decode_address in AddressCache.thy. Requires a `cache_abstraction`
  predicate relating near_arr + same_arr + near_ptr record field to
  the spec's `cache` record.

  Sketch:
    cache_abs s c near_ptr \<equiv>
       (\<forall>i<s_near. heap_w32 s (near_arr + int i) = of_nat (near c ! i)) \<and>
       (\<forall>i<same_buckets. heap_w32 s (same_arr + int i) = of_nat (same c ! i))

  Contract:
    {{ buf_valid ... ; mode \<le> 8; cache_abs s c near_ptr; addr_cache_ok c }}
      decode_address' patch addr_end pos here mode near_ptr
    {{ \<lambda>r s'. case r of
          Result ar \<Rightarrow>
             case decode_address c (unat mode) (unat here)
                     (drop (unat pos) (heap_bytes s patch (unat addr_end)))
             of Some (addr, rest, c') \<Rightarrow>
                  ar_t_C.pos_C ar = addr_end - of_nat (length rest)
                  \<and> ar_t_C.addr_C ar = of_nat addr
                  \<and> cache_abs s' c' (ar_t_C.near_ptr_C ar)
              | None \<Rightarrow> False
        | Exn e \<Rightarrow> ar_t_C.err_C e \<noteq> 0 \<and> s' = s }}

  The `finally` structure turns the "normal" flow into a throw that
  carries the final ar_t_C with err = 0, so the postcondition inverts
  Result/Exn compared to what it might naively look like.

  Builds on: read_byte'_spec, read_varint'_bounded (and eventually
  read_varint'_spec for full functional correctness).
*)

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
