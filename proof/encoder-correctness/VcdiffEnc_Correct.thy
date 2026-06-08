theory VcdiffEnc_Correct
  imports
    VcdiffEnc_Serialize
begin


(*
  Final composition point for encoder success correctness:

    vcdiff_encode' returns patch_len > 0
      \<Longrightarrow> decode_spec (heap_bytes post out patch_len) src_bytes = Inl tgt_bytes

  The component theories imported below are intentionally split by proof-team
  ownership so sub-lemmas can be completed in parallel worktrees.
*)

end
