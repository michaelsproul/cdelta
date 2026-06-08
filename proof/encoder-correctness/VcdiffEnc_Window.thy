theory VcdiffEnc_Window
  imports
    VcdiffEnc_Emit
    VcdiffEnc_Match
begin


(*
  Pure shape of the main encode_window loop invariant. The C-level invariant
  will add heap, cursor, cache, and capacity facts around this prefix split.
*)
definition encoder_loop_inv :: "byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> bool" where
  "encoder_loop_inv tgt tp flushed pending \<longleftrightarrow>
     tp \<le> length tgt \<and> flushed @ pending = take tp tgt"

lemma encoder_loop_invD:
  assumes "encoder_loop_inv tgt tp flushed pending"
  shows "tp \<le> length tgt" "flushed @ pending = take tp tgt"
  using assms by (simp_all add: encoder_loop_inv_def)

end
