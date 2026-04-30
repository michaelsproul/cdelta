theory VcdiffDec
  imports "AutoCorres2.AutoCorres"
begin

install_C_file "vcdiff_dec.c"

autocorres "vcdiff_dec.c"

context vcdiff_dec_global_addresses begin

thm vcdiff_decode'_def

end

end
