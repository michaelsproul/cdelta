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

(* ---------- read_varint refinement ---------- *)

(*
  read_varint' decodes a VCDIFF varint (up to 5 bytes) from `buf` starting
  at position `pos`. Under buffer validity, it refines the pure
  varint_decode against the byte list obtained from the heap.

  The C loop reads up to 5 bytes, shifting and OR'ing. Stops when it sees
  a byte with the high bit clear. Matches Varint.thy's varint_decode.
*)

end

end
