theory VcdiffEnc
  imports "AutoCorres2.AutoCorres"
begin

install_C_file "vcdiff_enc.c"

autocorres "vcdiff_enc.c"

context vcdiff_enc_global_addresses begin

thm vcdiff_varint_size'_def
thm vcdiff_varint_write'_def
thm vcdiff_encode_add'_def

end

end
