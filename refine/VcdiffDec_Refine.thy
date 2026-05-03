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
  TODO (read_varint'_spec): Hoare triple
    {{ buffer valid for [pos, len) ∧ len < 2^32 }}
       read_varint' buf len pos
    {{ λrv s'.
        case varint_decode (drop (unat pos) (heap_bytes s buf (unat len))) of
          Some (v, rest) ⇒
            rv = Result (pr_t_C (len - of_nat (length rest)) (of_nat v) 0)
        | None ⇒ error case }}

  Proof via whileLoop invariant relating (cur, i, v) to
  varint_decode_loop (5 - i) (unat v) (drop (unat cur - unat pos)
                                             (take (unat len) bytes)).

  Key challenge: the v bound ensures no 32-bit overflow; threading this
  through the invariant matches varint_decode_loop's "acc' < 2^32" check.
  Effort: ~1 week.
*)

(* ---------- decode_address refinement ---------- *)

(*
  TODO (decode_address'_spec): Hoare triple relating decode_address'
  (uses near_arr, same_arr file-scope caches) to the pure decode_address
  in AddressCache.thy. Requires invariant:
    cache_abstraction near_arr same_arr near_ptr = ⦇near = ..., same = ..., near_ptr = ...⦈
*)

(* ---------- build_code_table refinement ---------- *)

(*
  TODO (build_code_table'_spec): After build_code_table', the file-scope
  code_tbl matches default_entry pointwise. Small Hoare triple; the
  bookkeeping is all in translating the 256×6 byte array to default_entry
  values.
*)

(* ---------- vcdiff_decode' main refinement ---------- *)

(*
  TODO (vcdiff_decode'_spec): top-level refinement. Under the preconds
  of decode_c_refines_spec (see planning), prove:

    vcdiff_decode' patch patch_len src src_len out out_cap out_len_ptr \<bullet> s
      \<lbrace>\<lambda>rv s'.
        case decode_spec (heap_bytes s patch (unat patch_len))
                         (heap_bytes s src (unat src_len)) of
          Inl tgt ⇒ rv = Result VCD_OK
                   ∧ unat out_cap \<ge> length tgt
                   ∧ heap_bytes s' out (length tgt) = tgt
                   ∧ heap_w32 s' out_len_ptr = of_nat (length tgt)
                   ∧ (heap elsewhere unchanged)
        | Inr _ ⇒ rv \<noteq> Result VCD_OK \<rbrace>

  Proof structure: header parse, window header, then main while loop with
  invariant. The invariant is the largest piece: ties cursor positions
  to decode_loop state via encode_window_loop_decode_loop from the pure
  spec.
*)

end

end
