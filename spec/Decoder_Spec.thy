(*
  Pure VCDIFF decoder spec.

  Mirrors decoder/vcdiff_dec.c at the functional level. Structure:

    decode_spec patch src
      = do (header_info, patch') <- parse_header patch
           (win,        patch'') <- parse_window patch'
           apply_window win src

  We keep the parse_header / parse_window boundaries aligned with the C
  so the AutoCorres refinement at Layer B only has to relate one pure
  helper per C function.
*)
theory Decoder_Spec
  imports
    Bytes
    Varint
    AddressCache
    CodeTable
    Instructions
begin

unbundle bit_operations_syntax

(* ---------- Decode error model ---------- *)

datatype decode_error =
    E_TRUNC | E_MAGIC | E_HDR | E_WIN | E_DI | E_OPCODE | E_MODE
  | E_SIZE | E_OVERRUN | E_SRC | E_VARINT | E_OUTCAP | E_SRCNEED

(* ---------- Primitive byte-list parsers ---------- *)

definition pop_byte :: "byte list \<Rightarrow> (byte \<times> byte list) option" where
  "pop_byte bs = (case bs of [] \<Rightarrow> None | b # rest \<Rightarrow> Some (b, rest))"

(* ---------- Header parser ---------- *)

(* Returns the unconsumed tail after the 5-byte fixed header + optional
   app data. *)
definition parse_header :: "byte list \<Rightarrow> byte list + decode_error" where
  "parse_header bs =
     (case bs of
        b0 # b1 # b2 # b3 # hi # rest \<Rightarrow>
          if [b0, b1, b2, b3] \<noteq> [0xD6, 0xC3, 0xC4, 0x00]
          then Inr E_MAGIC
          else if hi AND 0x03 \<noteq> 0
          then Inr E_HDR
          else if hi AND 0x04 \<noteq> 0 then
            case varint_decode rest of
              None \<Rightarrow> Inr E_TRUNC
            | Some (app_len, rest') \<Rightarrow>
                if app_len \<le> length rest' then Inl (drop app_len rest')
                else Inr E_TRUNC
          else Inl rest
      | _ \<Rightarrow> Inr E_TRUNC)"

(* ---------- Window parser ---------- *)

record parsed_window =
  pw_src_seg_len :: nat
  pw_src_seg_off :: nat
  pw_tgt_len     :: nat
  pw_data        :: "byte list"
  pw_inst        :: "byte list"
  pw_addr        :: "byte list"

(* Accessor-style parser: reads the window header and sections, returning
   the unconsumed tail. *)
definition parse_window ::
    "byte list \<Rightarrow> (parsed_window \<times> byte list) + decode_error" where
  "parse_window bs =
     (case pop_byte bs of
        None \<Rightarrow> Inr E_TRUNC
      | Some (win_ind, bs1) \<Rightarrow>
          if win_ind AND 0x02 \<noteq> 0 then Inr E_WIN
          else if win_ind AND 0xFA \<noteq> 0 then Inr E_WIN
          else
            let has_src = (win_ind AND 0x01 \<noteq> 0) in
            (case (if has_src
                   then case varint_decode bs1 of
                          None \<Rightarrow> None
                        | Some (sl, bs2) \<Rightarrow>
                            (case varint_decode bs2 of
                               None \<Rightarrow> None
                             | Some (so, bs3) \<Rightarrow> Some (sl, so, bs3))
                   else Some (0, 0, bs1)) of
              None \<Rightarrow> Inr E_TRUNC
            | Some (src_seg_len, src_seg_off, bs3) \<Rightarrow>
                (case varint_decode bs3 of
                  None \<Rightarrow> Inr E_TRUNC
                | Some (dlen, bs4) \<Rightarrow>
                    (case varint_decode bs4 of
                      None \<Rightarrow> Inr E_TRUNC
                    | Some (tgt_len, bs5) \<Rightarrow>
                        (case pop_byte bs5 of
                          None \<Rightarrow> Inr E_TRUNC
                        | Some (di, bs6) \<Rightarrow>
                            if di \<noteq> 0 then Inr E_DI
                            else
                              (case varint_decode bs6 of
                                None \<Rightarrow> Inr E_TRUNC
                              | Some (data_len, bs7) \<Rightarrow>
                                  (case varint_decode bs7 of
                                    None \<Rightarrow> Inr E_TRUNC
                                  | Some (inst_len, bs8) \<Rightarrow>
                                      (case varint_decode bs8 of
                                        None \<Rightarrow> Inr E_TRUNC
                                      | Some (addr_len, bs9) \<Rightarrow>
                                          \<comment> \<open>No Adler32 in our encoder output; the C supports
                                              it but the spec doesn't emit it.\<close>
                                          if data_len + inst_len + addr_len > length bs9
                                          then Inr E_TRUNC
                                          else
                                            let data = take data_len bs9;
                                                rest1 = drop data_len bs9;
                                                inst = take inst_len rest1;
                                                rest2 = drop inst_len rest1;
                                                addr = take addr_len rest2;
                                                tail = drop addr_len rest2
                                            in Inl (\<lparr>
                                              pw_src_seg_len = src_seg_len,
                                              pw_src_seg_off = src_seg_off,
                                              pw_tgt_len     = tgt_len,
                                              pw_data        = data,
                                              pw_inst        = inst,
                                              pw_addr        = addr
                                            \<rparr>, tail)))))))))"

(* ---------- Instruction dispatch loop ---------- *)

(* State threaded through the decoder's main loop. *)
record dec_state =
  ds_data_rem :: "byte list"    \<comment> \<open>unread data-section bytes\<close>
  ds_inst_rem :: "byte list"    \<comment> \<open>unread inst-section bytes\<close>
  ds_addr_rem :: "byte list"    \<comment> \<open>unread addr-section bytes\<close>
  ds_cache    :: cache
  ds_tgt      :: "byte list"    \<comment> \<open>target built so far\<close>

(* Resolve a half-instruction's size. If the table entry has size=0 and
   type != NOOP, read a varint from the instruction stream. *)
definition resolve_size ::
    "half_inst \<Rightarrow> byte list \<Rightarrow> (nat \<times> byte list) option" where
  "resolve_size h bs =
     (if isz h = 0 \<and> ity h \<noteq> NOOP
      then varint_decode bs
      else Some (isz h, bs))"

(* Execute one half-instruction against a decoder state. Returns an error
   if data/addr cursors run out or the address is invalid. *)
definition exec_half ::
    "half_inst \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
     dec_state \<Rightarrow> dec_state + decode_error" where
  "exec_half h sz src_seg src_seg_len tgt_len st =
     (case ity h of
        NOOP \<Rightarrow> Inl st
      | IADD \<Rightarrow>
          if sz > length (ds_data_rem st) then Inr E_TRUNC
          else if length (ds_tgt st) + sz > tgt_len then Inr E_OVERRUN
          else
            Inl (st \<lparr> ds_data_rem := drop sz (ds_data_rem st)
                    , ds_tgt       := ds_tgt st @ take sz (ds_data_rem st) \<rparr>)
      | IRUN \<Rightarrow>
          (case pop_byte (ds_data_rem st) of
             None \<Rightarrow> Inr E_TRUNC
           | Some (b, rest) \<Rightarrow>
               if length (ds_tgt st) + sz > tgt_len then Inr E_OVERRUN
               else
                 Inl (st \<lparr> ds_data_rem := rest
                         , ds_tgt       := ds_tgt st @ replicate sz b \<rparr>))
      | ICOPY mode \<Rightarrow>
          let here = src_seg_len + length (ds_tgt st) in
          (case decode_address (ds_cache st) mode here (ds_addr_rem st) of
             None \<Rightarrow> Inr E_MODE
           | Some (addr, rest, c') \<Rightarrow>
               if addr + sz > src_seg_len + length (ds_tgt st) + sz
                  \<or> addr \<ge> src_seg_len + length (ds_tgt st) then Inr E_SRC
               else if length (ds_tgt st) + sz > tgt_len then Inr E_OVERRUN
               else
                 Inl (st \<lparr> ds_addr_rem := rest
                         , ds_cache    := c'
                         , ds_tgt      := copy_loop src_seg (ds_tgt st) addr sz \<rparr>)))"

(* Process one opcode from the instruction stream. *)
definition decode_one ::
    "byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dec_state \<Rightarrow> dec_state + decode_error" where
  "decode_one src_seg src_seg_len tgt_len st =
     (case pop_byte (ds_inst_rem st) of
        None \<Rightarrow> Inr E_TRUNC
      | Some (op, irest) \<Rightarrow>
          let (h1, h2) = default_entry (unat op);
              st1 = st \<lparr> ds_inst_rem := irest \<rparr>
          in
          (case resolve_size h1 (ds_inst_rem st1) of
             None \<Rightarrow> Inr E_TRUNC
           | Some (sz1, irest1) \<Rightarrow>
               let st2 = st1 \<lparr> ds_inst_rem := irest1 \<rparr> in
               (case exec_half h1 sz1 src_seg src_seg_len tgt_len st2 of
                  Inr e \<Rightarrow> Inr e
                | Inl st3 \<Rightarrow>
                    (case resolve_size h2 (ds_inst_rem st3) of
                       None \<Rightarrow> Inr E_TRUNC
                     | Some (sz2, irest2) \<Rightarrow>
                         let st4 = st3 \<lparr> ds_inst_rem := irest2 \<rparr> in
                         exec_half h2 sz2 src_seg src_seg_len tgt_len st4))))"

fun decode_loop ::
    "nat \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dec_state \<Rightarrow> dec_state + decode_error"
where
  "decode_loop 0 src_seg src_seg_len tgt_len st =
     (if ds_inst_rem st = [] then Inl st else Inr E_TRUNC)"
| "decode_loop (Suc fuel) src_seg src_seg_len tgt_len st =
     (if ds_inst_rem st = [] then Inl st
      else case decode_one src_seg src_seg_len tgt_len st of
             Inr e \<Rightarrow> Inr e
           | Inl st' \<Rightarrow> decode_loop fuel src_seg src_seg_len tgt_len st')"

(* ---------- Apply a parsed window ---------- *)

definition apply_window ::
    "parsed_window \<Rightarrow> byte list \<Rightarrow> byte list + decode_error" where
  "apply_window win src =
     (let src_seg_len = pw_src_seg_len win;
          src_seg_off = pw_src_seg_off win;
          src_seg = (if src_seg_len = 0 then []
                     else take src_seg_len (drop src_seg_off src));
          init_st = \<lparr> ds_data_rem = pw_data win
                    , ds_inst_rem = pw_inst win
                    , ds_addr_rem = pw_addr win
                    , ds_cache = cache_init
                    , ds_tgt = [] \<rparr>
      in if src_seg_len > 0 \<and> src_seg_off + src_seg_len > length src
         then Inr E_SRC
         else case decode_loop (length (pw_inst win)) src_seg src_seg_len
                  (pw_tgt_len win) init_st of
                Inr e \<Rightarrow> Inr e
              | Inl st \<Rightarrow>
                  if length (ds_tgt st) = pw_tgt_len win
                  then Inl (ds_tgt st)
                  else Inr E_SIZE)"

(* ---------- Top level ---------- *)

definition decode_spec ::
    "byte list \<Rightarrow> byte list \<Rightarrow> byte list + decode_error" where
  "decode_spec patch src =
     (case parse_header patch of
        Inr e \<Rightarrow> Inr e
      | Inl rest \<Rightarrow>
          (case parse_window rest of
             Inr e \<Rightarrow> Inr e
           | Inl wintail \<Rightarrow> apply_window (fst wintail) src))"

end
