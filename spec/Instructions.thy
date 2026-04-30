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
