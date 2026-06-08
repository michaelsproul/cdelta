theory VcdiffEnc_Wire
  imports
    VcdiffEnc_Writers
begin


(*
  Shared pure section-decoding predicates for the encoder proof.
  Encoder helper lemmas should preserve one of these predicates instead of
  depending on a concrete instruction-list serialization.
*)
definition section_decodes_prefix ::
  "byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
   cache \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> cache \<Rightarrow> bool" where
  "section_decodes_prefix src_seg tgt_len data inst addr c_in tgt_prefix target c_out \<longleftrightarrow>
     decode_loop (length inst) src_seg (length src_seg) tgt_len
       \<lparr> ds_data_rem = data
       , ds_inst_rem = inst
       , ds_addr_rem = addr
       , ds_cache = c_in
       , ds_tgt = tgt_prefix \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = c_out
           , ds_tgt = target \<rparr>"

definition section_decodes ::
  "byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
   byte list \<Rightarrow> cache \<Rightarrow> bool" where
  "section_decodes src_seg tgt_len data inst addr target c_out \<longleftrightarrow>
     section_decodes_prefix src_seg tgt_len data inst addr cache_init [] target c_out"

lemma section_decodesI:
  assumes "section_decodes_prefix src_seg tgt_len data inst addr cache_init [] target c_out"
  shows "section_decodes src_seg tgt_len data inst addr target c_out"
  using assms by (simp add: section_decodes_def)

lemma section_decodesD:
  assumes "section_decodes src_seg tgt_len data inst addr target c_out"
  shows "section_decodes_prefix src_seg tgt_len data inst addr cache_init [] target c_out"
  using assms by (simp add: section_decodes_def)

context vcdiff_enc_global_addresses begin


definition enc_sections_inv ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> sections_t_C \<Rightarrow>
   byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
   byte list \<Rightarrow> cache \<Rightarrow> bool" where
  "enc_sections_inv s data inst addr sec src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out \<longleftrightarrow>
     emitted_sections s data inst addr sec data_bytes inst_bytes addr_bytes \<and>
     section_decodes src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out"

lemma enc_sections_invD:
  assumes "enc_sections_inv s data inst addr sec src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out"
  shows "emitted_sections s data inst addr sec data_bytes inst_bytes addr_bytes"
        "section_decodes src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out"
  using assms by (simp_all add: enc_sections_inv_def)

end

end
