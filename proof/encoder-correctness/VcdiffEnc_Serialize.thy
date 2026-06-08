theory VcdiffEnc_Serialize
  imports
    VcdiffEnc_Window
begin

context vcdiff_enc_global_addresses begin

lemma varint_size'_less_128:
  fixes v :: "32 word"
  assumes v_lt: "v < 128"
  shows "varint_size' v s = Some 1"
proof -
  have shift0_unat: "unat (v >> (7 :: nat)) = 0"
    using v_lt
    by (simp add: Word_Lemmas.shiftr_div_2n' word_less_nat_alt)
  have shift0: "v >> (7 :: nat) = 0"
    using shift0_unat by (metis word_unat.Rep_inject unat_0)
  show ?thesis
    unfolding varint_size'_def
    by (simp add: shift0 Reader_Monad.owhile_def
                  Reader_Monad.obind_def Reader_Monad.oreturn_def
                  Reader_Monad.option_while_simps K_def)
qed

lemma varint_size'_0[simp]:
  "varint_size' 0 s = Some 1"
  by (rule varint_size'_less_128) simp

lemma varint_size'_5[simp]:
  "varint_size' 5 s = Some 1"
  by (rule varint_size'_less_128) simp

lemma varint_bytes32_0_1[simp]:
  "varint_bytes32 0 1 = [0]"
  by (simp add: varint_bytes32_def varint_byte32_def)

lemma varint_bytes32_5_1[simp]:
  "varint_bytes32 5 1 = [5]"
  by (simp add: varint_bytes32_def varint_byte32_def)

lemma serialize_empty:
  "serialize [] [] [] [] [] =
   [0xD6, 0xC3, 0xC4, 0, 0, 0, 5, 0, 0, 0, 0, 0]"
  by (simp add: serialize_def magic_bytes_def varint_encode_def
                varint_size_def to_base128_nonzero)

lemma serialize'_empty_writes_serialize:
  assumes cap: "(12 :: 32 word) \<le> out_cap"
      and out_valid: "buf_valid s out 12"
      and out_dist: "ptr_range_distinct out 12"
  shows "serialize' out out_cap 0 0 data 0 inst 0 addr 0 \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (12 :: 32 word) \<and>
                   heap_bytes t out 12 = serialize [] [] [] [] [] \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  unfolding serialize'_def
  apply runs_to_vcg
        apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
          apply (use cap in unat_arith)
         apply (insert buf_validD[OF out_valid, of 0])
         apply simp
        apply (rule ptr_range_distinct_mono[OF out_dist])
        apply simp
       apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
         apply (use cap in unat_arith)
        apply (insert buf_validD[OF out_valid, of 1])
        apply simp
       apply (rule ptr_range_distinct_mono[OF out_dist])
       apply simp
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
        apply (use cap in unat_arith)
       apply (insert buf_validD[OF out_valid, of 2])
       apply simp
      apply (rule ptr_range_distinct_mono[OF out_dist])
      apply simp
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
       apply (use cap in unat_arith)
      apply (insert buf_validD[OF out_valid, of 3])
      apply simp
     apply (rule ptr_range_distinct_mono[OF out_dist])
     apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
      apply (use cap in unat_arith)
     apply (insert buf_validD[OF out_valid, of 4])
     apply simp
    apply (rule ptr_range_distinct_mono[OF out_dist])
    apply simp
   apply clarsimp
   apply runs_to_vcg
   apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
     apply (use cap in unat_arith)
    apply (insert buf_validD[OF out_valid, of 5])
    apply simp
   apply (rule ptr_range_distinct_mono[OF out_dist])
   apply simp
  apply clarsimp
  apply runs_to_vcg
        apply (rule runs_to_weaken[
          OF write_varint'_success_heap_bytes_append_wordpos])
             apply simp
           apply (use cap in unat_arith)
           apply (intro allI impI)
           apply (insert buf_validD[OF out_valid, of 6])
           apply simp
         apply auto[1]
         apply (intro allI impI)
         apply (rule ptr_range_distinct_word_prefix_disj
           [where pos = 6 and len = 1 and total = 12, OF out_dist])
             apply simp
            apply simp
           apply assumption
          apply assumption
        apply simp
       apply clarsimp
       apply runs_to_vcg
       apply (rule runs_to_weaken[
         OF write_varint'_success_heap_bytes_append_wordpos])
            apply simp
          apply (use cap in unat_arith)
          apply (intro allI impI)
          apply (insert buf_validD[OF out_valid, of 7])
          apply simp
        apply auto[1]
        apply (intro allI impI)
        apply (rule ptr_range_distinct_word_prefix_disj
          [where pos = 7 and len = 1 and total = 12, OF out_dist])
            apply simp
           apply simp
          apply assumption
         apply assumption
       apply simp
      apply clarsimp
      apply runs_to_vcg
      apply (rule runs_to_weaken[OF write_byte'_heap_bytes_append_next_typing])
        apply (use cap in unat_arith)
       apply (insert buf_validD[OF out_valid, of 8])
       apply simp
      apply (rule ptr_range_distinct_mono[OF out_dist])
      apply simp
     apply clarsimp
     apply runs_to_vcg
     apply (rule runs_to_weaken[
       OF write_varint'_success_heap_bytes_append_wordpos])
          apply simp
        apply (use cap in unat_arith)
        apply (intro allI impI)
        apply (insert buf_validD[OF out_valid, of 9])
        apply simp
      apply auto[1]
      apply (intro allI impI)
      apply (rule ptr_range_distinct_word_prefix_disj
        [where pos = 9 and len = 1 and total = 12, OF out_dist])
          apply simp
         apply simp
        apply assumption
       apply assumption
     apply simp
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[
      OF write_varint'_success_heap_bytes_append_wordpos])
         apply simp
       apply (use cap in unat_arith)
       apply (intro allI impI)
       apply (insert buf_validD[OF out_valid, of 10])
       apply simp
     apply auto[1]
     apply (intro allI impI)
     apply (rule ptr_range_distinct_word_prefix_disj
       [where pos = 10 and len = 1 and total = 12, OF out_dist])
         apply simp
        apply simp
       apply assumption
      apply assumption
    apply simp
   apply clarsimp
   apply runs_to_vcg
   apply (rule runs_to_weaken[
     OF write_varint'_success_heap_bytes_append_wordpos])
        apply simp
      apply (use cap in unat_arith)
      apply (intro allI impI)
      apply (insert buf_validD[OF out_valid, of 11])
      apply simp
    apply auto[1]
    apply (intro allI impI)
    apply (rule ptr_range_distinct_word_prefix_disj
      [where pos = 11 and len = 1 and total = 12, OF out_dist])
        apply simp
       apply simp
      apply assumption
     apply assumption
   apply simp
  apply clarsimp
  apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_bytes'_zero])
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_bytes'_zero])
    apply clarsimp
    apply runs_to_vcg
    apply (rule runs_to_weaken[OF write_bytes'_zero])
    apply (clarsimp simp: serialize_empty heap_bytes_def)
  done

lemma serialize'_zero_lengths_writes_serialize:
  assumes cap: "(12 :: 32 word) \<le> out_cap"
      and out_valid: "buf_valid s out 12"
      and out_dist: "ptr_range_distinct out 12"
      and src_empty: "src = []"
      and tgt_empty: "tgt = []"
      and data_empty: "data_bytes = []"
      and inst_empty: "inst_bytes = []"
      and addr_empty: "addr_bytes = []"
  shows "serialize' out out_cap 0 0 data 0 inst 0 addr 0 \<bullet> s
           \<lbrace> \<lambda>r t. r = Result (12 :: 32 word) \<and>
                   heap_bytes t out 12 =
                     serialize src tgt data_bytes inst_bytes addr_bytes \<and>
                   heap_typing t = heap_typing s \<rbrace>"
  apply (rule runs_to_weaken[
    OF serialize'_empty_writes_serialize[OF cap out_valid out_dist]])
  using src_empty tgt_empty data_empty inst_empty addr_empty by simp

end

end
