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

session CdeltaEncoderCorrectness in "proof/encoder-correctness" = CdeltaEncoder +
  options [timeout = 1800, quick_and_dirty = true]
  sessions
    CdeltaSpecRoundtrip
  theories
    VcdiffEnc_Writers
    VcdiffEnc_Wire
    VcdiffEnc_Cache_Opcode
    VcdiffEnc_Match
    VcdiffEnc_Emit
    VcdiffEnc_Window
    VcdiffEnc_Serialize
    VcdiffEnc_Correct

session TestAdd in "proof/test-add" = AutoCorres2 +
  options [timeout = 600]
  theories
    Add

session CdeltaSpecRoundtrip in "proof/roundtrip" = CdeltaSpecBase +
  options [timeout = 1800, quick_and_dirty = false]
  theories
    Spec_Roundtrip

(*
  Image-only parent for CdeltaRefine. Exists so the Isabelle MCP
  (`isabelle vscode_server`) can be launched with `-l CdeltaRefineBase`
  and then re-elaborate VcdiffDec_Refine.thy live — if the MCP is
  launched with `-l CdeltaRefine` directly, PIDE considers the edited
  theory "already loaded" from the heap and refuses to produce goal
  state under the caret.
*)
session CdeltaRefineBase = CdeltaSpecRoundtrip +
  options [timeout = 1800, quick_and_dirty = false]
  sessions
    CdeltaDecoder
  theories
    "CdeltaDecoder.VcdiffDec"

session CdeltaRefine in "proof/decoder-refine" = CdeltaRefineBase +
  options [timeout = 1800, quick_and_dirty = true]
  theories
    VcdiffDec_Refine
