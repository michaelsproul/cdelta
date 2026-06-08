theory VcdiffEnc_Match
  imports
    VcdiffEnc_Cache_Opcode
begin


(*
  Match-quality predicate used by the future find_best_match proof: either
  no usable match was returned, or the source and target slices are equal.
*)
definition match_valid :: "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "match_valid src tgt tp pos len \<longleftrightarrow>
     (len = 0 \<or>
      pos + len \<le> length src \<and>
      tp + len \<le> length tgt \<and>
      take len (drop pos src) = take len (drop tp tgt))"

lemma match_valid_zero[simp]:
  "match_valid src tgt tp pos 0"
  by (simp add: match_valid_def)

end
