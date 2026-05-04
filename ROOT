(*
  Top-level session declarations for the cdelta verification project.

  Structure mirrors seL4's l4v: a single ROOT file declares every session
  and points to its directory via `in "..."`, so the Isabelle IDE finds
  the full session graph from any theory.

  Build everything from this directory:
      isabelle build -d . CdeltaRefine
*)

session CdeltaSpecBase in "spec/pure" = "HOL-Library" +
  options [timeout = 1800, quick_and_dirty = false]
  sessions
    "Word_Lib"
  theories
    Bytes
    Varint
    AddressCache
    CodeTable
    Instructions
    Encoder_Spec
    Decoder_Spec

session CdeltaDecoder in "spec/cdec" = AutoCorres2 +
  options [timeout = 600]
  theories
    VcdiffDec

session CdeltaEncoder in "spec/cenc" = AutoCorres2 +
  options [timeout = 600]
  theories
    VcdiffEnc

session TestAdd in "proof/test-add" = AutoCorres2 +
  options [timeout = 600]
  theories
    Add

session CdeltaSpecRoundtrip in "proof/roundtrip" = CdeltaSpecBase +
  options [timeout = 1800, quick_and_dirty = false]
  theories
    Spec_Roundtrip

session CdeltaRefine in "proof/decoder-refine" = CdeltaSpecRoundtrip +
  options [timeout = 1800, quick_and_dirty = false]
  sessions
    CdeltaDecoder
  theories
    VcdiffDec_Refine
