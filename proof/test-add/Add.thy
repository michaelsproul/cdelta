theory Add
  imports "AutoCorres2.AutoCorres"
begin

install_C_file "add.c"

autocorres "add.c"

context add_global_addresses begin

thm add'_def

lemma add'_is_plus: "add' a b = a + b"
  unfolding add'_def
  by simp

end

end
