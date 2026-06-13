theory VcdiffEnc_Correct
  imports
    VcdiffEnc_Serialize
begin

(*
  Final composition point for encoder success correctness. The proved
  lemmas below keep the pure part of the top-level theorem honest:
  once encode_window has produced sections that decode to the target, the
  existing serialize bridge and parser roundtrip imply decode_spec success.
*)

lemma section_decodes_apply_window:
  assumes dec:
    "section_decodes src (length tgt) data inst addr tgt c_out"
  shows "apply_window
           \<lparr> pw_src_seg_len = (if length src > 0 then length src else 0)
           , pw_src_seg_off = 0
           , pw_tgt_len = length tgt
           , pw_data = data, pw_inst = inst, pw_addr = addr \<rparr>
           src = Inl tgt"
  using dec
  by (cases "src = []")
     (simp_all add: apply_window_def Let_def section_decodes_def
       section_decodes_prefix_def)

lemma section_decodes_serialize_decode:
  assumes dec: "section_decodes src (length tgt) data inst addr tgt c_out"
      and src_bd: "length src < 2 ^ 32"
      and tgt_bd: "length tgt < 2 ^ 32 - 32"
      and data_bd: "length data < 2 ^ 32"
      and inst_bd: "length inst < 2 ^ 32"
      and addr_bd: "length addr < 2 ^ 32"
      and dlen_bd:
        "varint_size (length tgt) + 1 + varint_size (length data)
         + varint_size (length inst) + varint_size (length addr)
         + length data + length inst + length addr < 2 ^ 32"
  shows "decode_spec (serialize src tgt data inst addr) src = Inl tgt"
proof -
  have aw:
    "apply_window
       \<lparr> pw_src_seg_len = (if length src > 0 then length src else 0)
       , pw_src_seg_off = 0
       , pw_tgt_len = length tgt
       , pw_data = data, pw_inst = inst, pw_addr = addr \<rparr>
       src = Inl tgt"
    by (rule section_decodes_apply_window[OF dec])
  show ?thesis
    by (rule serialize_apply_window_roundtrip
      [OF src_bd tgt_bd data_bd inst_bd addr_bd dlen_bd aw])
qed

context vcdiff_enc_global_addresses begin

lemma enc_sections_inv_apply_window:
  assumes inv:
    "enc_sections_inv st data_p inst_p addr_p sec src (length tgt)
       data inst addr tgt c_out"
  shows "apply_window
           \<lparr> pw_src_seg_len = (if length src > 0 then length src else 0)
           , pw_src_seg_off = 0
           , pw_tgt_len = length tgt
           , pw_data = data, pw_inst = inst, pw_addr = addr \<rparr>
       src = Inl tgt"
  using section_decodes_apply_window[OF enc_sections_invD(2)[OF inv]] .

lemma encoder_sections_serialize_decode:
  assumes win:
    "enc_sections_inv st data_p inst_p addr_p sec src (length tgt)
       data inst addr tgt c_out"
      and src_bd: "length src < 2 ^ 32"
      and tgt_bd: "length tgt < 2 ^ 32 - 32"
      and data_bd: "length data < 2 ^ 32"
      and inst_bd: "length inst < 2 ^ 32"
      and addr_bd: "length addr < 2 ^ 32"
      and dlen_bd:
        "varint_size (length tgt) + 1 + varint_size (length data)
         + varint_size (length inst) + varint_size (length addr)
         + length data + length inst + length addr < 2 ^ 32"
  shows "decode_spec (serialize src tgt data inst addr) src = Inl tgt"
proof -
  show ?thesis
  by (rule section_decodes_serialize_decode
      [OF enc_sections_invD(2)[OF win] src_bd tgt_bd data_bd inst_bd addr_bd
          dlen_bd])
qed

(*
  Main window proof target. The loop invariant that should drive this is
  encode_window_c_loop_cache_inv from VcdiffEnc_Window:

    - pending-byte branch: encoder_loop_inv_pending_step_word plus a
      heap-byte write preservation fact for pending.
    - no-fusion COPY branch: flush_pending' preservation, then one of the
      four emit_copy' enc_sections/cache wrappers.
    - fused branch: try_emit_add_copy' fused preservation, followed by an
      optional remainder emit_copy' wrapper.
    - final flush: flush_pending' preservation and encoder_loop_inv_doneD.
*)
lemma encode_window'_after_cache_reset_success_enc_sections_cache_inv:
  fixes src_len tgt_len data_cap inst_cap addr_cap pending_cap :: "32 word"
  assumes reset_entry:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           encode_window_c_loop_cache_inv t
             src src_len tgt tgt_len head_p next_p
             data data_cap inst inst_cap addr addr_cap
             pending pending_cap (sections_t_C 0 0 0 0) 0 0
             src_bytes tgt_bytes [] [] [] [] [] cache_init \<and>
           heap_typing t = heap_typing s \<rbrace>"
  shows "encode_window' src src_len tgt tgt_len head_p next_p
           data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
          \<lbrace> \<lambda>r t. \<forall>sec. r = Result sec \<longrightarrow>
              sections_t_C.err_C sec = ENC_OK \<longrightarrow>
              (\<exists>data_bytes inst_bytes addr_bytes c_out.
                enc_sections_inv t data inst addr sec src_bytes (length tgt_bytes)
                  data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<rbrace>"
  unfolding encode_window'_def
  using reset_entry
  sorry

lemma encode_window'_success_enc_sections_cache_inv:
  fixes src_len tgt_len data_cap inst_cap addr_cap pending_cap :: "32 word"
  assumes src_len_eq: "length src_bytes = unat src_len"
      and tgt_len_eq: "length tgt_bytes = unat tgt_len"
      and src_heap: "heap_bytes s src (length src_bytes) = src_bytes"
      and tgt_heap: "heap_bytes s tgt (length tgt_bytes) = tgt_bytes"
  shows "encode_window' src src_len tgt tgt_len head_p next_p
           data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
          \<lbrace> \<lambda>r t. \<forall>sec. r = Result sec \<longrightarrow>
              sections_t_C.err_C sec = ENC_OK \<longrightarrow>
              (\<exists>data_bytes inst_bytes addr_bytes c_out.
                enc_sections_inv t data inst addr sec src_bytes (length tgt_bytes)
                  data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
                enc_cache_abs t c_out \<and>
                enc_cache_wf c_out) \<rbrace>"
proof -
  have reset_entry:
    "cache_reset' \<bullet> s
       \<lbrace> \<lambda>r t. r = Result () \<and>
           encode_window_c_loop_cache_inv t
             src src_len tgt tgt_len head_p next_p
             data data_cap inst inst_cap addr addr_cap
             pending pending_cap (sections_t_C 0 0 0 0) 0 0
             src_bytes tgt_bytes [] [] [] [] [] cache_init \<and>
           heap_typing t = heap_typing s \<rbrace>"
    by (rule cache_reset'_encode_window_c_loop_cache_inv_entry
      [OF src_len_eq tgt_len_eq src_heap tgt_heap])
  show ?thesis
    by (rule encode_window'_after_cache_reset_success_enc_sections_cache_inv
      [OF reset_entry])
qed

(*
  Public encoder theorem target. This composes:

    build_index correctness
    encode_window'_success_enc_sections_cache_inv
    serialize'_writes_serialize
    encoder_sections_serialize_decode
*)
lemma vcdiff_encode'_success_serialized_sections:
  fixes src_len tgt_len out_cap pending_cap data_cap inst_cap addr_cap :: "32 word"
  assumes src_len_eq: "length src_bytes = unat src_len"
      and tgt_len_eq: "length tgt_bytes = unat tgt_len"
      and src_heap: "heap_bytes s src (length src_bytes) = src_bytes"
      and tgt_heap: "heap_bytes s tgt (length tgt_bytes) = tgt_bytes"
  shows "vcdiff_encode' out out_cap src src_len tgt tgt_len head_p next_p
           pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
          \<lbrace> \<lambda>r t. \<forall>patch_len. r = Result patch_len \<longrightarrow>
              patch_len \<noteq> 0 \<longrightarrow>
              (\<exists>data_bytes inst_bytes addr_bytes c_out.
                section_decodes src_bytes (length tgt_bytes)
                  data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
                heap_bytes t out (unat patch_len) =
                  serialize src_bytes tgt_bytes data_bytes inst_bytes
                    addr_bytes \<and>
                length src_bytes < 2 ^ 32 \<and>
                length tgt_bytes < 2 ^ 32 - 32 \<and>
                length data_bytes < 2 ^ 32 \<and>
                length inst_bytes < 2 ^ 32 \<and>
                length addr_bytes < 2 ^ 32 \<and>
                varint_size (length tgt_bytes) + 1 +
                varint_size (length data_bytes) +
                varint_size (length inst_bytes) +
                varint_size (length addr_bytes) +
                length data_bytes + length inst_bytes + length addr_bytes
                  < 2 ^ 32) \<rbrace>"
proof -
  have window_slot:
    "encode_window' src src_len tgt tgt_len head_p next_p
       data data_cap inst inst_cap addr addr_cap pending pending_cap \<bullet> s
      \<lbrace> \<lambda>r t. \<forall>sec. r = Result sec \<longrightarrow>
          sections_t_C.err_C sec = ENC_OK \<longrightarrow>
          (\<exists>data_bytes inst_bytes addr_bytes c_out.
            enc_sections_inv t data inst addr sec src_bytes (length tgt_bytes)
              data_bytes inst_bytes addr_bytes tgt_bytes c_out \<and>
            enc_cache_abs t c_out \<and>
            enc_cache_wf c_out) \<rbrace>"
    by (rule encode_window'_success_enc_sections_cache_inv
      [OF src_len_eq tgt_len_eq src_heap tgt_heap])
  note serialize_slot = serialize'_writes_serialize
  show ?thesis
    using window_slot
    sorry
qed

theorem vcdiff_encode'_success_decode_spec:
  fixes src_len tgt_len out_cap pending_cap data_cap inst_cap addr_cap :: "32 word"
  assumes src_len_eq: "length src_bytes = unat src_len"
      and tgt_len_eq: "length tgt_bytes = unat tgt_len"
      and src_heap: "heap_bytes s src (length src_bytes) = src_bytes"
      and tgt_heap: "heap_bytes s tgt (length tgt_bytes) = tgt_bytes"
  shows "vcdiff_encode' out out_cap src src_len tgt tgt_len head_p next_p
           pending pending_cap data data_cap inst inst_cap addr addr_cap \<bullet> s
          \<lbrace> \<lambda>r t. \<forall>patch_len. r = Result patch_len \<longrightarrow>
              patch_len \<noteq> 0 \<longrightarrow>
              decode_spec (heap_bytes t out (unat patch_len)) src_bytes =
                Inl tgt_bytes \<rbrace>"
  apply (rule runs_to_weaken[
    OF vcdiff_encode'_success_serialized_sections
      [OF src_len_eq tgt_len_eq src_heap tgt_heap]])
  apply clarsimp
  subgoal premises prems for patch_len t data_bytes inst_bytes addr_bytes c_out
  proof -
    have src_bd: "length src_bytes < 2 ^ 32"
      using prems(4) by simp
    have tgt_bd: "length tgt_bytes < 2 ^ 32 - 32"
      using prems(5) by simp
    have data_bd_num: "length data_bytes < (4294967296 :: nat)"
      using prems(6) by linarith
    have data_bd: "length data_bytes < 2 ^ 32"
      using data_bd_num by simp
    have inst_bd_num: "length inst_bytes < (4294967296 :: nat)"
      using prems(6) by linarith
    have inst_bd: "length inst_bytes < 2 ^ 32"
      using inst_bd_num by simp
    have addr_bd_num: "length addr_bytes < (4294967296 :: nat)"
      using prems(6) by linarith
    have addr_bd: "length addr_bytes < 2 ^ 32"
      using addr_bd_num by simp
    have dlen_bd:
      "varint_size (length tgt_bytes) + 1 +
       varint_size (length data_bytes) +
       varint_size (length inst_bytes) +
       varint_size (length addr_bytes) +
       length data_bytes + length inst_bytes + length addr_bytes < 2 ^ 32"
    proof -
      have "varint_size (length tgt_bytes) + 1 +
        varint_size (length data_bytes) +
        varint_size (length inst_bytes) +
        varint_size (length addr_bytes) +
        length data_bytes + length inst_bytes + length addr_bytes
        < (4294967296 :: nat)"
        using prems(6) by linarith
      then show ?thesis by simp
    qed
    have dec:
      "decode_spec
        (serialize src_bytes tgt_bytes data_bytes inst_bytes addr_bytes)
        src_bytes = Inl tgt_bytes"
      by (rule section_decodes_serialize_decode
        [OF prems(2) src_bd tgt_bd data_bd inst_bd addr_bd dlen_bd])
    show ?thesis
      using dec prems(3) by simp
  qed
  done

end

end
