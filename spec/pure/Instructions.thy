(*
  Intermediate instruction stream between the encoder and decoder, plus an
  executable semantics that mirrors the C decoder's main loop.

  A `raw_inst` is the pre-wire representation of a single VCDIFF
  instruction: ADD carries the raw bytes, COPY carries the source-window
  address and length, RUN carries the repeated byte and length.

  exec_inst appends to the `target` byte list. COPY reads from the
  *combined window* = source segment followed by the target built so far,
  handling self-overlap correctly. This matches the C's COPY loop, which
  reads `out[tgt_rel]` for addresses past the source boundary.
*)
theory Instructions
  imports Bytes
begin

(* ---------- Raw instruction IR ---------- *)

datatype raw_inst =
    RAdd "byte list"
  | RCopy nat nat   \<comment> \<open>address, size\<close>
  | RRun byte nat

(* ---------- Combined-window byte access ---------- *)

(* byte at combined[pos] where combined = source ++ target_so_far. *)
definition combined_byte ::
    "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> byte" where
  "combined_byte src tgt pos =
     (if pos < length src then src ! pos
      else tgt ! (pos - length src))"

(*
  Copy n bytes from combined[addr..addr+n) onto the end of `tgt`. Byte-
  by-byte so that self-overlap (addr beyond original tgt size, but
  covered as copying proceeds) works: each new byte can extend the source
  for the next read, which is exactly the xdelta3 semantics RFC 3284
  relies on for RUN-like COPYs.
*)
fun copy_loop :: "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> byte list" where
  "copy_loop src tgt addr 0       = tgt"
| "copy_loop src tgt addr (Suc n) =
     copy_loop src (tgt @ [combined_byte src tgt addr]) (addr + 1) n"

(* ---------- exec_inst ---------- *)

(*
  Execute a single raw instruction against `target`, given `src` and the
  current `data_bytes` cursor. Returns the updated target and the
  remaining data bytes on success, None on malformed input.

  ADD consumes `length bs` bytes from data — but since RAdd already
  carries the bytes explicitly, we don't consume from `data` here; the
  caller chose to split at encoder time. RUN reads one byte and repeats.
  This shape keeps `exec_inst` total on its arguments and isolates
  section-length bookkeeping in the wire-format layer.
*)
fun exec_inst ::
    "byte list \<Rightarrow> raw_inst \<Rightarrow> byte list \<Rightarrow> byte list" where
  "exec_inst src (RAdd bs)       tgt = tgt @ bs"
| "exec_inst src (RRun b n)      tgt = tgt @ replicate n b"
| "exec_inst src (RCopy addr n)  tgt = copy_loop src tgt addr n"

fun exec_inst_list ::
    "byte list \<Rightarrow> raw_inst list \<Rightarrow> byte list \<Rightarrow> byte list" where
  "exec_inst_list src []       tgt = tgt"
| "exec_inst_list src (i # is) tgt = exec_inst_list src is (exec_inst src i tgt)"

(* ---------- Basic shape lemmas ---------- *)

lemma copy_loop_length:
  "length (copy_loop src tgt addr n) = length tgt + n"
  by (induction n arbitrary: tgt addr) auto

lemma exec_inst_add_length:
  "length (exec_inst src (RAdd bs) tgt) = length tgt + length bs"
  by simp

lemma exec_inst_run_length:
  "length (exec_inst src (RRun b n) tgt) = length tgt + n"
  by simp

lemma exec_inst_copy_length:
  "length (exec_inst src (RCopy addr n) tgt) = length tgt + n"
  by (simp add: copy_loop_length)

(* ---------- Validity predicate for COPY ---------- *)
(*
  The encoder must ensure the address is below the combined window and
  the span stays within addressable bytes. This is what lets copy_loop
  read from source or already-decoded target without running off the end
  — the encoder's matches are built from actual source/target bytes, so
  the addresses it generates are always valid.
*)
definition copy_valid ::
    "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "copy_valid src tgt addr n =
     (addr < length src + length tgt
    \<and> (\<forall>i < n. addr + i < length src + length tgt + i))"

(* ---------- Well-formedness of instruction lists ---------- *)
(*
  An instruction list is well-formed w.r.t. a source if every instruction is
  sensible at the point of emission:
    - ADD: non-empty payload
    - RUN: positive count
    - COPY: positive count, address < combined window at that point
  The partial target is threaded through because COPY validity depends on
  how much target has been built so far.
*)
fun wf_insts_aux :: "byte list \<Rightarrow> raw_inst list \<Rightarrow> byte list \<Rightarrow> bool" where
  "wf_insts_aux src [] tgt = True"
| "wf_insts_aux src (RAdd bs # is) tgt =
     (length bs > 0 \<and> wf_insts_aux src is (tgt @ bs))"
| "wf_insts_aux src (RRun b n # is) tgt =
     (n > 0 \<and> wf_insts_aux src is (tgt @ replicate n b))"
| "wf_insts_aux src (RCopy a n # is) tgt =
     (n > 0 \<and> a < length src + length tgt
    \<and> wf_insts_aux src is (copy_loop src tgt a n))"

definition wf_insts :: "byte list \<Rightarrow> raw_inst list \<Rightarrow> bool" where
  "wf_insts src insts = wf_insts_aux src insts []"

(*
  Combined validity: instructions are well-formed AND executing them on
  an empty target produces exactly tgt.
*)
definition valid_insts :: "byte list \<Rightarrow> byte list \<Rightarrow> raw_inst list \<Rightarrow> bool" where
  "valid_insts src tgt insts =
     (exec_inst_list src insts [] = tgt
    \<and> wf_insts src insts)"

(* The degenerate matcher [RAdd tgt] is always valid when tgt is non-empty
   (or even when it's empty, since length [] > 0 is False but the empty
   list case would need special handling). Actually for the general theorem
   we allow empty tgt via the empty instruction list. For [RAdd tgt] we
   need length tgt > 0. *)
lemma valid_insts_radd:
  assumes "length tgt > 0"
  shows "valid_insts src tgt [RAdd tgt]"
  using assms
  by (simp add: valid_insts_def wf_insts_def)

lemma valid_insts_nil:
  "valid_insts src [] []"
  by (simp add: valid_insts_def wf_insts_def)

(* ---------- Phase A.4 goal: exec preserves length and prefix invariance ---------- *)

(*
  An encoder-produced instruction stream, executed from a fresh target,
  yields exactly the encoder's original target byte list. Full statement
  lives at the encoder level (Encoder_Spec); here we only assert the
  shape-preserving lemmas, which are cheap.
*)

lemma exec_inst_length:
  "length (exec_inst src i tgt)
     = length tgt + (case i of RAdd bs \<Rightarrow> length bs
                              | RCopy _ n \<Rightarrow> n | RRun _ n \<Rightarrow> n)"
  by (cases i) (simp_all add: copy_loop_length)

lemma exec_inst_list_length:
  "length (exec_inst_list src is tgt)
     = length tgt + sum_list (map (\<lambda>i. case i of
          RAdd bs \<Rightarrow> length bs | RCopy _ n \<Rightarrow> n | RRun _ n \<Rightarrow> n) is)"
  by (induction "is" arbitrary: tgt) (simp_all add: exec_inst_length)

end
