(*
  Byte/word scaffolding shared by all cdelta specifications.

  The C code works in `unsigned int` throughout — 32 bits — with bytes being
  `unsigned char`. We model:
    - byte  = 8 word  (literal raw byte)
    - uint  = 32 word (used where the C does bitwise ops on unsigned int)
  and use `nat` for indices/sizes, carrying an explicit `< 2^32` bound in
  preconditions at the boundary with the C.

  We deliberately keep this theory small: its only job is to fix naming and
  provide a couple of ubiquitous abbreviations so downstream theories don't
  repeat them.
*)
theory Bytes
  imports
    "Word_Lib.Word_8"
    "Word_Lib.Word_32"
begin

type_synonym byte = "8 word"
type_synonym uint32 = "32 word"

(* Upper bounds corresponding to the C's unsigned-int arithmetic. Most
   downstream lemmas take `n < uint_max` as a precondition when they need
   to reason about wraparound-free arithmetic. *)
definition uint_max :: nat where
  "uint_max = 2 ^ 32"

lemma uint_max_pos [simp]: "0 < uint_max"
  by (simp add: uint_max_def)

(* A convenient varint bound: varints are capped at 5 bytes = 35 bits in the
   decoder, but the useful values fit in 32 bits. We use 2^35 for the
   "decoder accepts" bound and 2^32 for the "encoder produces" bound. *)
definition varint_max :: nat where
  "varint_max = 2 ^ 35"

lemma varint_max_pos [simp]: "0 < varint_max"
  by (simp add: varint_max_def)

lemma uint_max_le_varint_max: "uint_max \<le> varint_max"
  by (simp add: uint_max_def varint_max_def)

end
