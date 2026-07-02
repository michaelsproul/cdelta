theory VcdiffC_Roundtrip
  imports
    CdeltaEncoderCorrectness.VcdiffEnc_Serialize
    CdeltaRefine.VcdiffDec_Refine
begin

locale vcdiff_c_roundtrip_global_addresses =
  enc: vcdiff_enc_global_addresses +
  dec: vcdiff_dec_global_addresses
begin

definition decoder_input_from_encoder_output where
  "decoder_input_from_encoder_output enc_out enc_t enc_n dec_patch dec_src
      src_len src_bytes dec_s \<longleftrightarrow>
     dec.heap_bytes dec_s dec_patch (unat enc_n) =
       enc.heap_bytes enc_t enc_out (unat enc_n) \<and>
     dec.heap_bytes dec_s dec_src (unat src_len) = src_bytes"

definition decoder_roundtrip_runs where
  "decoder_roundtrip_runs dec_patch enc_n dec_src src_len dec_out dec_out_cap
      dec_out_len dec_s tgt_bytes \<longleftrightarrow>
     vcdiff_decode' dec_patch enc_n dec_src src_len dec_out dec_out_cap
       dec_out_len \<bullet> dec_s
     \<lbrace> \<lambda>dec_r dec_t.
          dec_r = Result (0 :: int) \<and>
          unat (heap_w32 dec_t dec_out_len) = length tgt_bytes \<and>
          dec.heap_bytes dec_t dec_out (length tgt_bytes) =
            tgt_bytes \<rbrace>"

lemma decode_spec_from_encoder_success:
  assumes enc_success:
    "enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n enc_s enc_t"
      and dec_input:
    "decoder_input_from_encoder_output enc_out enc_t enc_n dec_patch dec_src
       src_len src_bytes dec_s"
      and src_bound: "length src_bytes < 2 ^ 32"
      and tgt_bound: "length tgt_bytes < 2 ^ 32 - 32"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
  shows
    "decode_spec
       (dec.heap_bytes dec_s dec_patch (unat enc_n))
       (dec.heap_bytes dec_s dec_src (unat src_len)) =
     Inl tgt_bytes"
proof -
  have enc_n_len:
    "unat enc_n = length (encode_spec src_bytes tgt_bytes)"
    using enc_success by (simp add: enc.encoder_success_post_def)
  have enc_patch:
    "enc.heap_bytes enc_t enc_out (unat enc_n) =
      encode_spec src_bytes tgt_bytes"
    using enc_success enc_n_len by (simp add: enc.encoder_success_post_def)
  have dec_patch:
    "dec.heap_bytes dec_s dec_patch (unat enc_n) =
      encode_spec src_bytes tgt_bytes"
    using dec_input enc_patch
    by (simp add: decoder_input_from_encoder_output_def)
  have dec_src:
    "dec.heap_bytes dec_s dec_src (unat src_len) = src_bytes"
    using dec_input by (simp add: decoder_input_from_encoder_output_def)
  have roundtrip:
    "decode_spec (encode_spec src_bytes tgt_bytes) src_bytes = Inl tgt_bytes"
    by (rule spec_roundtrip[OF src_bound tgt_bound src_tgt_bound])
  show ?thesis
    using dec_patch dec_src roundtrip by simp
qed

lemma serialize_parse_window_source_bounds:
  assumes src_bound: "length src < 2 ^ 32"
      and parsed_header: "parse_header (serialize src tgt data inst addr) = Inl rest"
      and parsed_window: "parse_window rest = Inl (win, tail)"
  shows
    "pw_src_seg_off win \<le> length src \<and>
     pw_src_seg_len win \<le> length src - pw_src_seg_off win"
proof -
  let ?dlen = "varint_size (length tgt) + 1
      + varint_size (length data)
      + varint_size (length inst)
      + varint_size (length addr)
      + length data + length inst + length addr"
  let ?after =
    "varint_encode ?dlen
     @ varint_encode (length tgt)
     @ [0x00]
     @ varint_encode (length data)
     @ varint_encode (length inst)
     @ varint_encode (length addr)
     @ data @ inst @ addr"
  have rest_eq:
    "rest =
      (if length src > 0
       then (0x01 :: byte) #
         (varint_encode (length src) @ varint_encode 0 @ ?after)
       else (0x00 :: byte) # ?after)"
    using parsed_header
    by (auto simp: serialize_def parse_header_def magic_bytes_def Let_def)
  have src_decode:
    "varint_decode (varint_encode (length src) @ xs) =
      Some (length src, xs)" for xs
    using src_bound by (rule varint_decode_encode)
  have zero_decode:
    "varint_decode (varint_encode 0 @ xs) = Some (0, xs)" for xs
    using varint_decode_encode[of 0 xs] by simp
  show ?thesis
  proof (cases "length src > 0")
    case True
    have fields:
      "pw_src_seg_len win = length src"
      "pw_src_seg_off win = 0"
      using parsed_window rest_eq True src_decode zero_decode
      by (auto simp: parse_window_def pop_byte_def Let_def
          split: option.splits if_splits)
    then show ?thesis by simp
  next
    case False
    have fields:
      "pw_src_seg_len win = 0"
      "pw_src_seg_off win = 0"
      using parsed_window rest_eq False
      by (auto simp: parse_window_def pop_byte_def Let_def
          split: option.splits if_splits)
    then show ?thesis by simp
  qed
qed

lemma encode_spec_parse_window_source_bounds:
  assumes src_bound: "length src < 2 ^ 32"
      and parsed_header: "parse_header (encode_spec src tgt) = Inl rest"
      and parsed_window: "parse_window rest = Inl (win, tail)"
  shows
    "pw_src_seg_off win \<le> length src \<and>
     pw_src_seg_len win \<le> length src - pw_src_seg_off win"
proof -
  let ?full = "encode_window_full_spec src tgt"
  show ?thesis
  proof (cases "sections_fit_32 src tgt ?full")
    case True
    then have enc_eq:
      "encode_spec src tgt =
        serialize src tgt (efr_data ?full) (efr_inst ?full) (efr_addr ?full)"
      by (simp add: encode_spec_alt Let_def)
    show ?thesis
      by (rule serialize_parse_window_source_bounds[
          OF src_bound _ parsed_window])
        (use parsed_header enc_eq in simp)
  next
    case False
    obtain data inst addr cache where enc_window:
      "encode_window (generate_instructions src tgt) (length src) =
        (data, inst, addr, cache)"
      by (cases "encode_window (generate_instructions src tgt) (length src)") auto
    have enc_eq:
      "encode_spec src tgt = serialize src tgt data inst addr"
      using False enc_window
      by (simp add: encode_spec_alt encode_spec_run_alt Let_def)
    show ?thesis
      by (rule serialize_parse_window_source_bounds[
          OF src_bound _ parsed_window])
        (use parsed_header enc_eq in simp)
  qed
qed

lemma serialize_parse_window_source_target_fit:
  assumes src_bound: "length src < 2 ^ 32"
      and tgt_bound: "length tgt < 2 ^ 32"
      and dlen_bound:
    "varint_size (length tgt) + 1
     + varint_size (length data)
     + varint_size (length inst)
     + varint_size (length addr)
     + length data + length inst + length addr < 2 ^ 32"
      and src_tgt_bound: "length src + length tgt < 2 ^ 32"
      and parsed_header: "parse_header (serialize src tgt data inst addr) = Inl rest"
      and parsed_window: "parse_window rest = Inl (win, tail)"
  shows "pw_src_seg_len win + pw_tgt_len win < 2 ^ 32"
proof -
  let ?dlen = "varint_size (length tgt) + 1
      + varint_size (length data)
      + varint_size (length inst)
      + varint_size (length addr)
      + length data + length inst + length addr"
  let ?after =
    "varint_encode ?dlen
     @ varint_encode (length tgt)
     @ [0x00]
     @ varint_encode (length data)
     @ varint_encode (length inst)
     @ varint_encode (length addr)
     @ data @ inst @ addr"
  have rest_eq:
    "rest =
      (if length src > 0
       then (0x01 :: byte) #
         (varint_encode (length src) @ varint_encode 0 @ ?after)
       else (0x00 :: byte) # ?after)"
    using parsed_header
    by (auto simp: serialize_def parse_header_def magic_bytes_def Let_def)
  have src_decode:
    "varint_decode (varint_encode (length src) @ xs) =
      Some (length src, xs)" for xs
    using src_bound by (rule varint_decode_encode)
  have zero_decode:
    "varint_decode (varint_encode 0 @ xs) = Some (0, xs)" for xs
    using varint_decode_encode[of 0 xs] by simp
  have dlen_decode:
    "varint_decode (varint_encode ?dlen @ xs) = Some (?dlen, xs)" for xs
    using dlen_bound by (rule varint_decode_encode)
  have tgt_decode:
    "varint_decode (varint_encode (length tgt) @ xs) =
      Some (length tgt, xs)" for xs
    using tgt_bound by (rule varint_decode_encode)
  show ?thesis
  proof (cases "length src > 0")
    case True
    have fields:
      "pw_src_seg_len win = length src"
      "pw_tgt_len win = length tgt"
      using parsed_window rest_eq True src_decode zero_decode dlen_decode
        tgt_decode
      by (auto simp: parse_window_def pop_byte_def Let_def
          split: option.splits if_splits)
    then show ?thesis
      using src_tgt_bound by simp
  next
    case False
    have fields:
      "pw_src_seg_len win = 0"
      "pw_tgt_len win = length tgt"
      using parsed_window rest_eq False dlen_decode tgt_decode
      by (auto simp: parse_window_def pop_byte_def Let_def
          split: option.splits if_splits)
    then show ?thesis
      using src_tgt_bound by simp
  qed
qed

lemma encode_spec_parse_window_source_target_fit:
  assumes src_bound: "length src < 2 ^ 32"
      and tgt_bound: "length tgt < 2 ^ 32 - 32"
      and src_tgt_bound: "length src + length tgt < 2 ^ 32"
      and parsed_header: "parse_header (encode_spec src tgt) = Inl rest"
      and parsed_window: "parse_window rest = Inl (win, tail)"
  shows "pw_src_seg_len win + pw_tgt_len win < 2 ^ 32"
proof -
  let ?full = "encode_window_full_spec src tgt"
  have tgt_bound32: "length tgt < 2 ^ 32"
    using tgt_bound by simp
  show ?thesis
  proof (cases "sections_fit_32 src tgt ?full")
    case True
    have enc_eq:
      "encode_spec src tgt =
        serialize src tgt (efr_data ?full) (efr_inst ?full) (efr_addr ?full)"
      using True by (simp add: encode_spec_alt Let_def)
    have dlen_bound:
      "varint_size (length tgt) + 1
       + varint_size (length (efr_data ?full))
       + varint_size (length (efr_inst ?full))
       + varint_size (length (efr_addr ?full))
       + length (efr_data ?full) + length (efr_inst ?full)
       + length (efr_addr ?full) < 2 ^ 32"
      using True by (simp add: sections_fit_32_def)
    show ?thesis
      by (rule serialize_parse_window_source_target_fit[
          OF src_bound tgt_bound32 dlen_bound src_tgt_bound
             _ parsed_window])
        (use parsed_header enc_eq in simp)
  next
    case False
    let ?insts = "generate_instructions src tgt"
    obtain data inst addr c where ew:
      "encode_window ?insts (length src) = (data, inst, addr, c)"
      by (cases "encode_window ?insts (length src)") auto
    have ew_run:
      "encode_window (generate_run_instructions tgt) (length src) =
        (data, inst, addr, c)"
      using ew by (simp add: generate_instructions_def)
    have lens:
      "length data \<le> length tgt"
      "length inst \<le> 1 + varint_size (length tgt)"
      "addr = []"
      using encode_window_generate_run_instructions_bounds[OF ew_run] by auto
    have data_bound: "length data < 2 ^ 32"
      using lens(1) tgt_bound32 by linarith
    have addr_bound: "length addr < 2 ^ 32"
      using lens(3) by simp
    have vsz_tgt: "varint_size (length tgt) \<le> 5"
      by (rule varint_size_le_5_32[OF tgt_bound32])
    have inst_bound: "length inst < 2 ^ 32"
    proof -
      have "length inst \<le> 6"
        using lens(2) vsz_tgt by linarith
      then show ?thesis by simp
    qed
    have vsz_data: "varint_size (length data) \<le> 5"
      by (rule varint_size_le_5_32[OF data_bound])
    have vsz_inst: "varint_size (length inst) \<le> 5"
      by (rule varint_size_le_5_32[OF inst_bound])
    have vsz_addr: "varint_size (length addr) \<le> 1"
      using lens(3) by (simp add: varint_size_def)
    have addr_len: "length addr = 0"
      using lens(3) by simp
    have dlen_le:
      "varint_size (length tgt) + 1
       + varint_size (length data)
       + varint_size (length inst)
       + varint_size (length addr)
       + length data + length inst + length addr
       \<le> 23 + length tgt"
      using lens addr_len vsz_tgt vsz_data vsz_inst vsz_addr by linarith
    have dlen_bound:
      "varint_size (length tgt) + 1
       + varint_size (length data)
       + varint_size (length inst)
       + varint_size (length addr)
       + length data + length inst + length addr < 2 ^ 32"
      using dlen_le tgt_bound by linarith
    have enc_eq:
      "encode_spec src tgt = serialize src tgt data inst addr"
      using False ew
      by (simp add: encode_spec_alt encode_spec_run_alt Let_def)
    show ?thesis
      by (rule serialize_parse_window_source_target_fit[
          OF src_bound tgt_bound32 dlen_bound src_tgt_bound
             _ parsed_window])
        (use parsed_header enc_eq in simp)
  qed
qed

lemma encode_spec_source_windows_in_bounds:
  fixes src_len :: "32 word"
  assumes enc_success:
    "enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n enc_s enc_t"
      and dec_input:
    "decoder_input_from_encoder_output enc_out enc_t enc_n dec_patch dec_src
       src_len src_bytes dec_s"
      and src_len_eq: "unat src_len = length src_bytes"
  shows
    "\<And>rest win tail.
       parse_header (dec.heap_bytes dec_s dec_patch (unat enc_n)) =
         Inl rest \<Longrightarrow>
       parse_window rest = Inl (win, tail) \<Longrightarrow>
       pw_src_seg_off win \<le> unat src_len \<and>
       pw_src_seg_len win \<le> unat src_len - pw_src_seg_off win"
proof -
  have enc_n_len:
    "unat enc_n = length (encode_spec src_bytes tgt_bytes)"
    using enc_success by (simp add: enc.encoder_success_post_def)
  have enc_patch:
    "enc.heap_bytes enc_t enc_out (unat enc_n) =
      encode_spec src_bytes tgt_bytes"
    using enc_success enc_n_len by (simp add: enc.encoder_success_post_def)
  have dec_patch:
    "dec.heap_bytes dec_s dec_patch (unat enc_n) =
      encode_spec src_bytes tgt_bytes"
    using dec_input enc_patch
    by (simp add: decoder_input_from_encoder_output_def)
  have src_bound: "length src_bytes < 2 ^ 32"
    using src_len_eq unat_lt2p[of src_len] by simp
  fix rest win tail
  assume parsed_header:
    "parse_header (dec.heap_bytes dec_s dec_patch (unat enc_n)) =
      Inl rest"
    and parsed_window: "parse_window rest = Inl (win, tail)"
  have bounds:
    "pw_src_seg_off win \<le> length src_bytes \<and>
     pw_src_seg_len win \<le> length src_bytes - pw_src_seg_off win"
    by (rule encode_spec_parse_window_source_bounds[OF src_bound])
      (use parsed_header parsed_window dec_patch in simp_all)
  show
    "pw_src_seg_off win \<le> unat src_len \<and>
     pw_src_seg_len win \<le> unat src_len - pw_src_seg_off win"
    using bounds src_len_eq by simp
qed

lemma encode_spec_source_target_window_fits:
  fixes src_len :: "32 word"
  assumes enc_success:
    "enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n enc_s enc_t"
      and dec_input:
    "decoder_input_from_encoder_output enc_out enc_t enc_n dec_patch dec_src
       src_len src_bytes dec_s"
      and src_len_eq: "unat src_len = length src_bytes"
      and tgt_bound: "length tgt_bytes < 2 ^ 32 - 32"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
  shows
    "\<And>rest win tail.
       parse_header (dec.heap_bytes dec_s dec_patch (unat enc_n)) =
         Inl rest \<Longrightarrow>
       parse_window rest = Inl (win, tail) \<Longrightarrow>
       pw_src_seg_len win + pw_tgt_len win < 2 ^ 32"
proof -
  have enc_n_len:
    "unat enc_n = length (encode_spec src_bytes tgt_bytes)"
    using enc_success by (simp add: enc.encoder_success_post_def)
  have enc_patch:
    "enc.heap_bytes enc_t enc_out (unat enc_n) =
      encode_spec src_bytes tgt_bytes"
    using enc_success enc_n_len by (simp add: enc.encoder_success_post_def)
  have dec_patch:
    "dec.heap_bytes dec_s dec_patch (unat enc_n) =
      encode_spec src_bytes tgt_bytes"
    using dec_input enc_patch
    by (simp add: decoder_input_from_encoder_output_def)
  have src_bound: "length src_bytes < 2 ^ 32"
    using src_len_eq unat_lt2p[of src_len] by simp
  fix rest win tail
  assume parsed_header:
    "parse_header (dec.heap_bytes dec_s dec_patch (unat enc_n)) =
      Inl rest"
    and parsed_window: "parse_window rest = Inl (win, tail)"
  show "pw_src_seg_len win + pw_tgt_len win < 2 ^ 32"
    by (rule encode_spec_parse_window_source_target_fit[
        OF src_bound tgt_bound src_tgt_bound])
      (use parsed_header parsed_window dec_patch in simp_all)
qed

theorem vcdiff_encoded_patch_decodes_to_target_topdown:
  fixes dec_patch dec_src dec_out :: "8 word ptr"
    and src_len enc_n dec_out_cap :: "32 word"
    and dec_out_len :: "32 word ptr"
  assumes enc_success:
    "enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n enc_s enc_t"
      and dec_input:
    "decoder_input_from_encoder_output enc_out enc_t enc_n dec_patch dec_src
       src_len src_bytes dec_s"
      and src_len_eq: "unat src_len = length src_bytes"
      and src_bound: "length src_bytes < 2 ^ 32"
      and tgt_bound: "length tgt_bytes < 2 ^ 32 - 32"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and out_len_ok: "ptr_valid (heap_typing dec_s) dec_out_len"
      and patch_ok:
    "dec.buf_valid dec_s dec_patch (unat enc_n)"
      and src_ok:
    "dec.buf_valid dec_s dec_src (unat src_len)"
      and src_nonnull: "dec_src \<noteq> NULL"
      and out_ok:
    "dec.buf_valid dec_s dec_out (length tgt_bytes)"
      and code_tbl_matches_ready: "dec.code_tbl_matches dec_s"
      and code_tbl_tags_ready: "dec.code_tbl_tags_valid dec_s"
      and out_patch_disj:
    "\<forall>i < length tgt_bytes. \<forall>j < unat enc_n.
       dec_out +\<^sub>p int i \<noteq> dec_patch +\<^sub>p int j"
      and out_src_disj:
    "\<forall>i < length tgt_bytes. \<forall>j < unat src_len.
       dec_out +\<^sub>p int i \<noteq> dec_src +\<^sub>p int j"
      and out_inj:
    "\<forall>i < length tgt_bytes. \<forall>j < length tgt_bytes.
       i \<noteq> j \<longrightarrow> dec_out +\<^sub>p int i \<noteq> dec_out +\<^sub>p int j"
      and out_cap_enough: "length tgt_bytes \<le> unat dec_out_cap"
  shows
    "vcdiff_decode' dec_patch enc_n dec_src src_len dec_out dec_out_cap
       dec_out_len \<bullet> dec_s
     \<lbrace> \<lambda>r dec_t.
          r = Result (0 :: int) \<and>
          unat (heap_w32 dec_t dec_out_len) = length tgt_bytes \<and>
          dec.heap_bytes dec_t dec_out (length tgt_bytes) =
            tgt_bytes \<rbrace>"
proof -
  have source_windows_in_bounds:
    "\<And>rest win tail.
       parse_header (dec.heap_bytes dec_s dec_patch (unat enc_n)) =
         Inl rest \<Longrightarrow>
       parse_window rest = Inl (win, tail) \<Longrightarrow>
       pw_src_seg_off win \<le> unat src_len \<and>
       pw_src_seg_len win \<le> unat src_len - pw_src_seg_off win"
    by (rule encode_spec_source_windows_in_bounds[
        OF enc_success dec_input src_len_eq])
  have source_target_window_fits:
    "\<And>rest win tail.
       parse_header (dec.heap_bytes dec_s dec_patch (unat enc_n)) =
         Inl rest \<Longrightarrow>
       parse_window rest = Inl (win, tail) \<Longrightarrow>
       pw_src_seg_len win + pw_tgt_len win < 2 ^ 32"
    by (rule encode_spec_source_target_window_fits[
        OF enc_success dec_input src_len_eq tgt_bound src_tgt_bound])
  have decode_ok:
    "decode_spec
       (dec.heap_bytes dec_s dec_patch (unat enc_n))
       (dec.heap_bytes dec_s dec_src (unat src_len)) =
     Inl tgt_bytes"
    by (rule decode_spec_from_encoder_success[
        OF enc_success dec_input src_bound tgt_bound src_tgt_bound])
  show ?thesis
    by (rule dec.vcdiff_decode'_spec_inl[
        OF out_len_ok patch_ok src_ok src_nonnull out_ok
           code_tbl_matches_ready code_tbl_tags_ready out_patch_disj
           out_src_disj out_inj out_cap_enough source_windows_in_bounds
           source_target_window_fits decode_ok])
qed

lemma vcdiff_encode'_writes_encode_spec_roundtrip_context:
  fixes enc_out enc_src enc_tgt enc_pending enc_data enc_inst enc_addr ::
      "8 word ptr"
    and enc_out_cap enc_src_len enc_tgt_len enc_pending_cap enc_data_cap
      enc_inst_cap enc_addr_cap :: "32 word"
    and enc_head_arr enc_next_arr :: "32 word ptr"
  assumes input:
    "enc.encoder_input_rel enc_s enc_src enc_src_len enc_tgt enc_tgt_len
       src_bytes tgt_bytes"
      and buffers:
    "enc.encoder_buffers_ok enc_s enc_out enc_out_cap enc_src enc_src_len enc_tgt
       enc_tgt_len enc_head_arr enc_next_arr enc_pending enc_pending_cap
       enc_data enc_data_cap enc_inst enc_inst_cap enc_addr enc_addr_cap"
      and pending_cap_ok: "unat enc_tgt_len \<le> unat enc_pending_cap"
      and src_len_word:
    "unat enc_src_len < unat (no_entry32 :: 32 word)"
      and head_valid:
    "\<And>h. h < hash_size \<Longrightarrow>
       vcdiff_enc.ptr_valid (VcdiffEnc.lifted_globals.heap_typing enc_s)
         (enc_head_arr +\<^sub>p int h)"
      and next_valid:
    "\<And>p. p < unat enc_src_len \<Longrightarrow>
       vcdiff_enc.ptr_valid (VcdiffEnc.lifted_globals.heap_typing enc_s)
         (enc_next_arr +\<^sub>p int p)"
      and head_no_alias:
    "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
       enc_head_arr +\<^sub>p int h \<noteq> enc_head_arr +\<^sub>p int bucket"
      and next_no_alias:
    "\<And>q p. \<lbrakk>q < unat enc_src_len; p < unat enc_src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
       enc_next_arr +\<^sub>p int q \<noteq> enc_next_arr +\<^sub>p int p"
      and next_head_disjoint:
    "\<And>h p. \<lbrakk>h < hash_size; p < unat enc_src_len\<rbrakk> \<Longrightarrow>
       enc_head_arr +\<^sub>p int h \<noteq> enc_next_arr +\<^sub>p int p"
      and head_next_disjoint:
    "\<And>q bucket. \<lbrakk>q < unat enc_src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
       enc_next_arr +\<^sub>p int q \<noteq> enc_head_arr +\<^sub>p int bucket"
      and fit:
    "sections_fit_32 src_bytes tgt_bytes
       (encode_window_full_spec src_bytes tgt_bytes)"
      and enc_out_cap_ok:
    "length (encode_spec src_bytes tgt_bytes) \<le> unat enc_out_cap"
      and encoded_len_word:
    "length (encode_spec src_bytes tgt_bytes) < 2 ^ 32"
  shows
    "vcdiff_encode' enc_out enc_out_cap enc_src enc_src_len enc_tgt
       enc_tgt_len enc_head_arr enc_next_arr enc_pending enc_pending_cap
       enc_data enc_data_cap enc_inst enc_inst_cap enc_addr enc_addr_cap \<bullet>
       enc_s
     \<lbrace> \<lambda>r enc_t.
          \<exists>enc_n.
            r = Result enc_n \<and>
            enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n enc_s
              enc_t \<rbrace>"
  apply (rule enc.vcdiff_encode'_writes_encode_spec_topdown)
              apply (rule input)
             apply (rule buffers)
            apply (rule pending_cap_ok)
           apply (rule src_len_word)
          apply (blast intro: head_valid)
         apply (blast intro: next_valid)
        apply (metis head_no_alias)
       apply (metis next_no_alias)
      apply (metis next_head_disjoint)
     apply (metis head_next_disjoint)
    apply (rule fit)
   apply (rule enc_out_cap_ok)
  apply (rule encoded_len_word)
  done

theorem vcdiff_encode'_then_decode_roundtrip_topdown:
  fixes enc_out enc_src enc_tgt enc_pending enc_data enc_inst enc_addr ::
      "8 word ptr"
    and enc_out_cap enc_src_len enc_tgt_len enc_pending_cap enc_data_cap
      enc_inst_cap enc_addr_cap :: "32 word"
    and enc_head_arr enc_next_arr :: "32 word ptr"
    and dec_patch dec_src dec_out :: "8 word ptr"
    and dec_out_cap :: "32 word"
    and dec_out_len :: "32 word ptr"
  assumes input:
    "enc.encoder_input_rel enc_s enc_src enc_src_len enc_tgt enc_tgt_len
       src_bytes tgt_bytes"
      and buffers:
    "enc.encoder_buffers_ok enc_s enc_out enc_out_cap enc_src enc_src_len enc_tgt
       enc_tgt_len enc_head_arr enc_next_arr enc_pending enc_pending_cap
       enc_data enc_data_cap enc_inst enc_inst_cap enc_addr enc_addr_cap"
      and pending_cap_ok: "unat enc_tgt_len \<le> unat enc_pending_cap"
      and src_len_word:
    "unat enc_src_len < unat (no_entry32 :: 32 word)"
      and head_valid:
    "\<And>h. h < hash_size \<Longrightarrow>
       vcdiff_enc.ptr_valid (VcdiffEnc.lifted_globals.heap_typing enc_s)
         (enc_head_arr +\<^sub>p int h)"
      and next_valid:
    "\<And>p. p < unat enc_src_len \<Longrightarrow>
       vcdiff_enc.ptr_valid (VcdiffEnc.lifted_globals.heap_typing enc_s)
         (enc_next_arr +\<^sub>p int p)"
      and head_no_alias:
    "\<And>h bucket. \<lbrakk>h < hash_size; bucket < hash_size; h \<noteq> bucket\<rbrakk> \<Longrightarrow>
       enc_head_arr +\<^sub>p int h \<noteq> enc_head_arr +\<^sub>p int bucket"
      and next_no_alias:
    "\<And>q p. \<lbrakk>q < unat enc_src_len; p < unat enc_src_len; q \<noteq> p\<rbrakk> \<Longrightarrow>
       enc_next_arr +\<^sub>p int q \<noteq> enc_next_arr +\<^sub>p int p"
      and next_head_disjoint:
    "\<And>h p. \<lbrakk>h < hash_size; p < unat enc_src_len\<rbrakk> \<Longrightarrow>
       enc_head_arr +\<^sub>p int h \<noteq> enc_next_arr +\<^sub>p int p"
      and head_next_disjoint:
    "\<And>q bucket. \<lbrakk>q < unat enc_src_len; bucket < hash_size\<rbrakk> \<Longrightarrow>
       enc_next_arr +\<^sub>p int q \<noteq> enc_head_arr +\<^sub>p int bucket"
      and fit:
    "sections_fit_32 src_bytes tgt_bytes
       (encode_window_full_spec src_bytes tgt_bytes)"
      and enc_out_cap_ok:
    "length (encode_spec src_bytes tgt_bytes) \<le> unat enc_out_cap"
      and encoded_len_word:
    "length (encode_spec src_bytes tgt_bytes) < 2 ^ 32"
      and src_len_eq: "unat enc_src_len = length src_bytes"
      and src_bound: "length src_bytes < 2 ^ 32"
      and tgt_bound: "length tgt_bytes < 2 ^ 32 - 32"
      and src_tgt_bound: "length src_bytes + length tgt_bytes < 2 ^ 32"
      and dec_input:
    "\<And>enc_n enc_t. enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n
       enc_s enc_t \<Longrightarrow>
       decoder_input_from_encoder_output enc_out enc_t enc_n dec_patch dec_src
         enc_src_len src_bytes dec_s"
      and out_len_ok: "ptr_valid (heap_typing dec_s) dec_out_len"
      and patch_ok:
    "\<And>enc_n enc_t. enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n
       enc_s enc_t \<Longrightarrow>
       dec.buf_valid dec_s dec_patch (unat enc_n)"
      and src_ok:
    "dec.buf_valid dec_s dec_src (unat enc_src_len)"
      and src_nonnull: "dec_src \<noteq> NULL"
      and out_ok:
    "dec.buf_valid dec_s dec_out (length tgt_bytes)"
      and code_tbl_matches_ready: "dec.code_tbl_matches dec_s"
      and code_tbl_tags_ready: "dec.code_tbl_tags_valid dec_s"
      and out_patch_disj:
    "\<And>enc_n enc_t. enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n
       enc_s enc_t \<Longrightarrow>
       \<forall>i < length tgt_bytes. \<forall>j < unat enc_n.
         dec_out +\<^sub>p int i \<noteq> dec_patch +\<^sub>p int j"
      and out_src_disj:
    "\<forall>i < length tgt_bytes. \<forall>j < unat enc_src_len.
       dec_out +\<^sub>p int i \<noteq> dec_src +\<^sub>p int j"
      and out_inj:
    "\<forall>i < length tgt_bytes. \<forall>j < length tgt_bytes.
       i \<noteq> j \<longrightarrow> dec_out +\<^sub>p int i \<noteq> dec_out +\<^sub>p int j"
      and dec_out_cap_enough: "length tgt_bytes \<le> unat dec_out_cap"
  shows
    "vcdiff_encode' enc_out enc_out_cap enc_src enc_src_len enc_tgt
       enc_tgt_len enc_head_arr enc_next_arr enc_pending enc_pending_cap
       enc_data enc_data_cap enc_inst enc_inst_cap enc_addr enc_addr_cap \<bullet>
       enc_s
     \<lbrace> \<lambda>r enc_t.
          \<exists>enc_n.
            r = Result enc_n \<and>
            decoder_roundtrip_runs dec_patch enc_n dec_src enc_src_len
              dec_out dec_out_cap dec_out_len dec_s tgt_bytes \<rbrace>"
proof (rule runs_to_weaken[
    OF vcdiff_encode'_writes_encode_spec_roundtrip_context[
      OF input buffers pending_cap_ok src_len_word head_valid next_valid
         head_no_alias next_no_alias next_head_disjoint head_next_disjoint
         fit enc_out_cap_ok encoded_len_word]])
  fix r enc_t
  assume post:
    "\<exists>n. r = Result n \<and>
      enc.encoder_success_post enc_out src_bytes tgt_bytes n enc_s enc_t"
  then obtain enc_n where
      r_def: "r = Result enc_n"
    and enc_success:
      "enc.encoder_success_post enc_out src_bytes tgt_bytes enc_n enc_s enc_t"
    by blast
  have dec_run:
    "decoder_roundtrip_runs dec_patch enc_n dec_src enc_src_len dec_out
       dec_out_cap dec_out_len dec_s tgt_bytes"
    unfolding decoder_roundtrip_runs_def
    by (rule vcdiff_encoded_patch_decodes_to_target_topdown[
        OF enc_success dec_input[OF enc_success] src_len_eq src_bound
           tgt_bound src_tgt_bound out_len_ok patch_ok[OF enc_success]
           src_ok src_nonnull out_ok code_tbl_matches_ready
           code_tbl_tags_ready out_patch_disj[OF enc_success] out_src_disj
           out_inj dec_out_cap_enough])
  show "\<exists>enc_n.
      r = Result enc_n \<and>
      decoder_roundtrip_runs dec_patch enc_n dec_src enc_src_len dec_out
        dec_out_cap dec_out_len dec_s tgt_bytes"
    using r_def dec_run by blast
qed

end

end
