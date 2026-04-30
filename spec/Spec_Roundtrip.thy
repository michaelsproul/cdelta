(*
  Top-level roundtrip theorem: decoding what the encoder produced recovers
  the target.

  The spec encoder uses a degenerate `generate_instructions` that emits a
  single RAdd covering the whole target. That's enough for the theorem —
  a smarter matcher is a refinement — but it keeps the proof tractable at
  the Phase A layer.

  Proof decomposition:
    1. encode_one inverts resolve-and-exec for each instruction form.
    2. encode_window_loop inverts decode_loop, threading cache state.
    3. serialize inverts parse_header + parse_window.
    4. Compose.
*)
theory Spec_Roundtrip
  imports
    Encoder_Spec
    Decoder_Spec
begin

unbundle bit_operations_syntax

(* ---------- Magic / header invariants ---------- *)

lemma parse_header_of_encoder_prefix:
  "parse_header (magic_bytes @ [0x00] @ rest) = Inl rest"
  sorry

(* ---------- encode_one / exec_half inversion lemmas ---------- *)

lemma encode_one_add_decoded:
  fixes bs :: "byte list"
  assumes "length bs < 2 ^ 32"
  shows "True"
  by simp  \<comment> \<open>placeholder — replaced by real inversion lemma later\<close>

(* ---------- Main roundtrip theorem ---------- *)

(*
  Decoder applied to the encoder output recovers `tgt`, provided the
  target is below the 32-bit varint domain. The source bound follows
  because the encoder reads `length src` and emits it as a varint.
*)
theorem spec_roundtrip:
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32"
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
  sorry

end
