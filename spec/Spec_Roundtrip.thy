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

(* ---------- Header roundtrip ---------- *)
(*
  The encoder prepends a fixed 5-byte prefix (magic + 0x00 version + 0x00
  Hdr_Indicator). parse_header recovers the tail.
*)
lemma parse_header_of_magic:
  "parse_header (magic_bytes @ 0x00 # rest) = Inl rest"
proof -
  have mg: "magic_bytes @ 0x00 # rest = 0xD6 # 0xC3 # 0xC4 # 0x00 # 0x00 # rest"
    by (simp add: magic_bytes_def)
  show ?thesis
    by (simp add: parse_header_def mg)
qed

(* ---------- encode_one for a single ADD of size 1..17 ---------- *)
(*
  Specialised lemma: if the encoder emits a single ADD of small size, the
  decoder reads exactly one opcode from the instruction section, no
  varint, and appends all the data bytes to the target.
*)

lemma encode_one_add_small:
  assumes "1 \<le> length bs" "length bs \<le> 17"
  shows "encode_one (RAdd bs) src_len tgt_pos c [] [] []
       = (bs, [word_of_nat (1 + length bs) :: byte], [], c, tgt_pos + length bs)"
  using assms
  by (simp add: find_single_add_opcode_def Let_def split_def)

(* Core instruction-level roundtrip: one ADD of small size. *)
lemma decode_one_add_small:
  assumes "1 \<le> sz" "sz \<le> 17"
          "data = bs" "length bs = sz"
  shows
    "decode_one src_seg src_seg_len sz
       \<lparr> ds_data_rem = data
       , ds_inst_rem = (word_of_nat (1 + sz) :: byte) # []
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = [] \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
proof -
  let ?op = "word_of_nat (1 + sz) :: byte"
  have op_lt: "1 + sz < 256" using assms(2) by simp
  have unat_op: "unat (word_of_nat (1 + sz) :: byte) = 1 + sz"
    using op_lt by (subst unat_of_nat_eq) simp_all
  have unat_op_alt: "unat (1 + word_of_nat sz :: byte) = 1 + sz"
  proof -
    have "(1 :: byte) + word_of_nat sz = word_of_nat (1 + sz)"
      by simp
    thus ?thesis using unat_op by simp
  qed
  have entry: "default_entry (unat ?op) = (add_hi sz, noop_hi)"
    using default_entry_add_small[OF assms(1,2)] unat_op by simp
  have entry_alt: "default_entry (unat (1 + word_of_nat sz :: byte)) = (add_hi sz, noop_hi)"
    using default_entry_add_small[OF assms(1,2)] unat_op_alt by simp
  have sz_pos: "sz > 0" using assms(1) by simp
  have len_data: "length data = sz" using assms(3,4) by simp
  have not_over_data: "\<not> sz > length data" using len_data by simp
  have not_over_tgt: "\<not> (length ([] :: byte list) + sz > sz)" by simp
  have resolve_add: "resolve_size (add_hi sz) [] = Some (sz, [])"
    using sz_pos by (simp add: resolve_size_def add_hi_def)
  have resolve_noop: "resolve_size noop_hi [] = Some (0, [])"
    by (simp add: resolve_size_def noop_hi_def)
  have take_bs: "take sz data = bs" using assms(3,4) by simp
  have drop_bs: "drop sz data = []" using assms(3,4) by simp
  have exec_half_add:
    "exec_half (add_hi sz) sz src_seg src_seg_len sz
       \<lparr> ds_data_rem = data
       , ds_inst_rem = []
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = [] \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
    using not_over_data take_bs drop_bs
    by (simp add: exec_half_def add_hi_def)
  have exec_half_noop:
    "exec_half noop_hi 0 src_seg src_seg_len sz
       \<lparr> ds_data_rem = []
       , ds_inst_rem = []
       , ds_addr_rem = []
       , ds_cache = cache_init
       , ds_tgt = bs \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = cache_init
           , ds_tgt = bs \<rparr>"
    by (simp add: exec_half_def noop_hi_def)
  show ?thesis
    unfolding decode_one_def
    by (simp add: pop_byte_def Let_def entry_alt resolve_add exec_half_add
                  resolve_noop exec_half_noop)
qed

(* ---------- encode_spec for a target of length 1..17 and empty source ---------- *)
(*
  For very small cases we can show decode inverts encode by direct
  computation. This is a sanity check that the pipeline composes.
*)
lemma encode_window_small_empty_src:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
  shows
    "encode_window [RAdd tgt] 0
       = (tgt, [word_of_nat (1 + length tgt) :: byte], [], cache_init)"
proof -
  have eo: "encode_one (RAdd tgt) 0 0 cache_init [] [] []
              = (tgt, [word_of_nat (1 + length tgt) :: byte], [],
                 cache_init, length tgt)"
    using encode_one_add_small[OF assms, where src_len = 0 and tgt_pos = 0 and c = cache_init]
    by simp
  show ?thesis
    using eo by (simp add: encode_window_def split_def)
qed

(* ---------- Top-level theorem ---------- *)

(*
  Decoder applied to the encoder output recovers `tgt`, provided the
  target is below the 32-bit varint domain. The source bound follows
  because the encoder reads `length src` and emits it as a varint.

  The full proof for arbitrary (src, tgt) requires tracking every branch
  of encode_one / decode_one through the wire format. Here we state the
  intended theorem; a concrete discharge is deferred to the full
  instruction-dispatch-loop correctness lemma, which is the largest
  remaining piece of the pure spec.

  For now we only prove the theorem for the empty-source, small-target
  regime where the encoder emits a single small ADD. That's sufficient
  to exercise the header / window / instruction / data layers end-to-end.
*)
(*
  The encoder, with the degenerate single-RAdd matcher, produces a
  concrete serialized byte list. Here we state and prove the shape of
  the output for the small (1..17) target, empty-source case.

  NB: for this lemma we only need the list-shape equation; the varint
  roundtrip is exercised transitively by parse_window.
*)
lemma encode_spec_small_empty_shape:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
  shows "encode_spec [] tgt =
           magic_bytes @ [0x00, 0x00]
         @ varint_encode (1 + varint_size (length tgt) + varint_size (length tgt)
                         + varint_size 1 + varint_size 0
                         + length tgt + 1)
         @ varint_encode (length tgt)
         @ [0x00]
         @ varint_encode (length tgt)
         @ varint_encode 1
         @ varint_encode 0
         @ tgt
         @ [word_of_nat (1 + length tgt) :: byte]"
  using encode_window_small_empty_src[OF assms]
  by (simp add: encode_spec_def generate_instructions_def serialize_def Let_def
                split_def magic_bytes_def add.commute add.left_commute)

theorem spec_roundtrip_small:
  assumes "1 \<le> length tgt" "length tgt \<le> 17"
          "length tgt < 2 ^ 32"
  shows   "decode_spec (encode_spec [] tgt) [] = Inl tgt"
  sorry  \<comment> \<open>Remaining gap: parse_window on the serialized output is the
            one big missing step. Proof is mechanical (repeated
            varint_decode_encode) but each step requires unfolding a
            deeply nested case-expression, and the total length of the
            explicit proof script exceeds what's useful overnight. See
            planning/spec-progress.md.\<close>

theorem spec_roundtrip:
  assumes "length src < 2 ^ 32"
          "length tgt < 2 ^ 32"
  shows   "decode_spec (encode_spec src tgt) src = Inl tgt"
  sorry  \<comment> \<open>General form; requires the full instruction-dispatch loop
            correctness proof for arbitrary-length targets and sources.\<close>

end
