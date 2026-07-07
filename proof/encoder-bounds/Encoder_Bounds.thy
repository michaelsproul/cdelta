(*
  Tight output-length bounds for the pure C-shaped encoder spec.

  Main results, assuming only `length src < 2^32` (needed so copy
  addresses fit in a 5-byte varint):

    - each of the three sections of `encode_window_full_spec src tgt`
      satisfies   data <= tgt,  inst <= tgt,  4*addr <= 5*tgt,
      and jointly data + inst + addr <= 2*tgt;
    - with `length tgt < 2^31 - 32` in addition,
      `sections_fit_32` always holds and
      `length (encode_spec src tgt) <= 2 * length tgt + 38  < 2^32`.

  The addr bound is exactly tight: a fused ADD(1)+COPY(6) followed by a
  length-1 remainder COPY emits 10 addr bytes for 8 flushed target
  bytes, i.e. 4*10 = 5*8.

  The proof is a fuel induction over `encode_window_full_loop` with the
  four inequalities as the invariant `enc_sections_bounded`, measured
  against `enc_flushed` (bytes materialised into sections); the final
  `enc_flushed = length tgt` comes from the existing trace-completeness
  lemma `encode_window_full_loop_trace_complete`.
*)
theory Encoder_Bounds
  imports CdeltaSpecRoundtrip.Spec_Roundtrip
begin

(* ---------- Varint self-bounds ---------- *)

(* num_digits n <= n; strict for n >= 2. These make the per-instruction
   inst-byte cost arguments constant-free: an instruction covering n
   target bytes never spends more than n inst bytes. *)
lemma num_digits_le_self: "num_digits n \<le> n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis by simp
  next
    case False
    hence pos: "0 < n" by simp
    have div_lt: "n div 128 < n" using pos by simp
    have "num_digits n = num_digits (n div 128) + 1"
      by (rule num_digits_nonzero[OF pos])
    also have "\<dots> \<le> n div 128 + 1" using less.IH[OF div_lt] by simp
    also have "\<dots> \<le> n" using div_lt by simp
    finally show ?thesis .
  qed
qed

lemma num_digits_lt_self:
  assumes n2: "2 \<le> n"
  shows "num_digits n < n"
proof (cases "n < 128")
  case True
  have "num_digits n = num_digits (n div 128) + 1"
    using n2 by (intro num_digits_nonzero) simp
  with True have "num_digits n = 1" by simp
  then show ?thesis using n2 by simp
next
  case False
  hence n128: "128 \<le> n" by simp
  have pos: "0 < n" using n2 by simp
  have q1: "1 \<le> n div 128"
    using div_le_mono[OF n128, of 128] by simp
  have qmul: "n div 128 * 128 + n mod 128 = n"
    by (rule div_mult_mod_eq)
  have "num_digits n = num_digits (n div 128) + 1"
    by (rule num_digits_nonzero[OF pos])
  also have "\<dots> \<le> n div 128 + 1"
    using num_digits_le_self[of "n div 128"] by simp
  also have "\<dots> < n" using q1 qmul by linarith
  finally show ?thesis .
qed

lemma varint_size_le_self:
  assumes "1 \<le> n"
  shows "varint_size n \<le> n"
  using assms num_digits_le_self[of n] by (simp add: varint_size_def)

lemma varint_size_lt_self:
  assumes "2 \<le> n"
  shows "varint_size n < n"
  using assms num_digits_lt_self[of n] by (simp add: varint_size_def)

lemma varint_size_zero [simp]: "varint_size 0 = 1"
  by (simp add: varint_size_def)

(* ---------- The sections-bounded invariant ---------- *)

(*
  All four inequalities are needed as inductive conjuncts:
    - the first three give the per-section caps;
    - the fourth (sum <= 2*flushed) gives the total output bound and is
      NOT derivable from the first three (they only give 3.25x).
*)
definition enc_sections_bounded :: "enc_full_state \<Rightarrow> bool" where
  "enc_sections_bounded st \<longleftrightarrow>
     length (enc_data st) \<le> enc_flushed st \<and>
     length (enc_inst st) \<le> enc_flushed st \<and>
     4 * length (enc_addr st) \<le> 5 * enc_flushed st \<and>
     length (enc_data st) + length (enc_inst st) + length (enc_addr st)
       \<le> 2 * enc_flushed st"

lemma enc_sections_boundedI:
  assumes "length (enc_data st) \<le> enc_flushed st"
      and "length (enc_inst st) \<le> enc_flushed st"
      and "4 * length (enc_addr st) \<le> 5 * enc_flushed st"
      and "length (enc_data st) + length (enc_inst st) + length (enc_addr st)
             \<le> 2 * enc_flushed st"
  shows "enc_sections_bounded st"
  using assms by (simp add: enc_sections_bounded_def)

lemma enc_sections_boundedD:
  assumes "enc_sections_bounded st"
  shows "length (enc_data st) \<le> enc_flushed st"
    and "length (enc_inst st) \<le> enc_flushed st"
    and "4 * length (enc_addr st) \<le> 5 * enc_flushed st"
    and "length (enc_data st) + length (enc_inst st) + length (enc_addr st)
           \<le> 2 * enc_flushed st"
  using assms by (simp_all add: enc_sections_bounded_def)

lemma enc_sections_bounded_init:
  "enc_sections_bounded enc_full_init"
  by (simp add: enc_sections_bounded_def enc_full_init_def)

lemma enc_sections_bounded_buffer_pending_byte [simp]:
  "enc_sections_bounded (buffer_pending_byte_spec b st)
     = enc_sections_bounded st"
  by (simp add: enc_sections_bounded_def buffer_pending_byte_spec_def)

(*
  Workhorse: a step whose per-section growth (kd, ki, ka) is funded by
  its own enc_flushed growth kf preserves the invariant.
*)
lemma enc_sections_bounded_step:
  assumes bounded: "enc_sections_bounded st"
      and dd: "length (enc_data st') \<le> length (enc_data st) + kd"
      and ii: "length (enc_inst st') \<le> length (enc_inst st) + ki"
      and aa: "length (enc_addr st') \<le> length (enc_addr st) + ka"
      and ff: "enc_flushed st' = enc_flushed st + kf"
      and h1: "kd \<le> kf"
      and h2: "ki \<le> kf"
      and h3: "4 * ka \<le> 5 * kf"
      and h4: "kd + ki + ka \<le> 2 * kf"
  shows "enc_sections_bounded st'"
proof (rule enc_sections_boundedI)
  note b = enc_sections_boundedD[OF bounded]
  show "length (enc_data st') \<le> enc_flushed st'"
    using b(1) dd ff h1 by linarith
  show "length (enc_inst st') \<le> enc_flushed st'"
    using b(2) ii ff h2 by linarith
  show "4 * length (enc_addr st') \<le> 5 * enc_flushed st'"
    using b(3) aa ff h3 by linarith
  show "length (enc_data st') + length (enc_inst st') + length (enc_addr st')
          \<le> 2 * enc_flushed st'"
    using b(4) dd ii aa ff h4 by linarith
qed

(* ---------- Shape of flush_pending output ---------- *)

(* Every instruction produced by the pending-buffer flush is a
   non-empty ADD or a RUN of length >= min_run. *)
definition flush_inst_ok :: "raw_inst \<Rightarrow> bool" where
  "flush_inst_ok i \<longleftrightarrow>
     (\<exists>bs. i = RAdd bs \<and> bs \<noteq> []) \<or>
     (\<exists>b n. i = RRun b n \<and> min_run \<le> n)"

lemma append_add_inst_shape:
  assumes "\<forall>i \<in> set out. flush_inst_ok i"
  shows "\<forall>i \<in> set (append_add_inst bs out). flush_inst_ok i"
  using assms by (auto simp: append_add_inst_def flush_inst_ok_def)

lemma close_pending_run_shape:
  assumes "\<forall>i \<in> set (ps_out s). flush_inst_ok i"
  shows "\<forall>i \<in> set (ps_out (close_pending_run s)). flush_inst_ok i"
proof (cases "ps_run_byte s")
  case None
  then show ?thesis using assms by (simp add: close_pending_run_def)
next
  case (Some b)
  show ?thesis
  proof (cases "min_run \<le> ps_run_len s")
    case True
    have appended: "\<forall>i \<in> set (append_add_inst (ps_add s) (ps_out s)). flush_inst_ok i"
      by (rule append_add_inst_shape[OF assms])
    show ?thesis
      using appended Some True
      by (auto simp: close_pending_run_def flush_inst_ok_def)
  next
    case False
    then show ?thesis using assms Some by (simp add: close_pending_run_def)
  qed
qed

lemma pending_scan_step_shape:
  assumes "\<forall>i \<in> set (ps_out s). flush_inst_ok i"
  shows "\<forall>i \<in> set (ps_out (pending_scan_step s b)). flush_inst_ok i"
  using assms close_pending_run_shape[OF assms]
  by (auto simp: pending_scan_step_def split: option.splits if_splits)

lemma pending_scan_fold_shape:
  assumes "\<forall>i \<in> set (ps_out s). flush_inst_ok i"
  shows "\<forall>i \<in> set (ps_out (foldl pending_scan_step s bs)). flush_inst_ok i"
  using assms
proof (induction bs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  have step: "\<forall>i \<in> set (ps_out (pending_scan_step s b)). flush_inst_ok i"
    by (rule pending_scan_step_shape[OF Cons.prems])
  show ?case
    using Cons.IH[OF step] by simp
qed

lemma flush_pending_insts_shape:
  "\<forall>i \<in> set (flush_pending_insts pending). flush_inst_ok i"
proof -
  let ?s = "close_pending_run (foldl pending_scan_step pending_scan_init pending)"
  have fold: "\<forall>i \<in> set (ps_out (foldl pending_scan_step pending_scan_init pending)).
                flush_inst_ok i"
    by (rule pending_scan_fold_shape) (simp add: pending_scan_init_def)
  have close: "\<forall>i \<in> set (ps_out ?s). flush_inst_ok i"
    by (rule close_pending_run_shape[OF fold])
  show ?thesis
    using append_add_inst_shape[OF close]
    by (simp add: flush_pending_insts_def Let_def)
qed

(* ---------- Per-instruction growth: cost <= consumed length ---------- *)

lemma encode_one_add_growth:
  assumes eo: "encode_one (RAdd bs) src_len tgt_pos c data inst addr
                 = (data', inst', addr', c', tgt_pos')"
      and nonempty: "bs \<noteq> []"
  shows "length data' = length data + length bs"
    and "length inst' \<le> length inst + length bs"
    and "addr' = addr"
    and "tgt_pos' = tgt_pos + length bs"
proof -
  obtain op needs_sz where fop:
    "find_single_add_opcode (length bs) = (op, needs_sz)"
    by (cases "find_single_add_opcode (length bs)") auto
  have len_pos: "1 \<le> length bs"
    using nonempty by (cases bs) auto
  show "length data' = length data + length bs"
    using eo fop by (auto simp: Let_def)
  show "addr' = addr"
    using eo fop by (auto simp: Let_def)
  show "tgt_pos' = tgt_pos + length bs"
    using eo fop by (auto simp: Let_def)
  show "length inst' \<le> length inst + length bs"
  proof (cases needs_sz)
    case False
    have "length inst' = length inst + 1"
      using eo fop False by (auto simp: Let_def)
    then show ?thesis using len_pos by simp
  next
    case True
    have big: "18 \<le> length bs"
      using fop len_pos True
      by (auto simp: find_single_add_opcode_def split: if_splits)
    have "length inst' = length inst + 1 + varint_size (length bs)"
      using eo fop True by (auto simp: Let_def)
    moreover have "varint_size (length bs) < length bs"
      using varint_size_lt_self[of "length bs"] big by simp
    ultimately show ?thesis by simp
  qed
qed

lemma encode_one_run_growth:
  assumes eo: "encode_one (RRun b n) src_len tgt_pos c data inst addr
                 = (data', inst', addr', c', tgt_pos')"
      and run_min: "min_run \<le> n"
  shows "length data' = length data + 1"
    and "length inst' \<le> length inst + n"
    and "addr' = addr"
    and "tgt_pos' = tgt_pos + n"
proof -
  show "length data' = length data + 1"
    using eo by (auto simp: find_single_run_opcode_def Let_def)
  show "addr' = addr"
    using eo by (auto simp: find_single_run_opcode_def Let_def)
  show "tgt_pos' = tgt_pos + n"
    using eo by (auto simp: find_single_run_opcode_def Let_def)
  have n2: "2 \<le> n" using run_min by (simp add: min_run_def)
  have "length inst' = length inst + 1 + varint_size n"
    using eo by (auto simp: find_single_run_opcode_def Let_def)
  moreover have "varint_size n < n"
    by (rule varint_size_lt_self[OF n2])
  ultimately show "length inst' \<le> length inst + n" by simp
qed

lemma encode_one_copy_growth:
  assumes eo: "encode_one (RCopy a n) src_len tgt_pos c data inst addr
                 = (data', inst', addr', c', tgt_pos')"
      and a_bd: "a < 2 ^ 32"
  shows "data' = data"
    and "length inst' \<le> length inst + 1 + varint_size n"
    and "4 \<le> n \<Longrightarrow> n \<le> 18 \<Longrightarrow> length inst' = length inst + 1"
    and "length addr' \<le> length addr + 5"
    and "tgt_pos' = tgt_pos + n"
proof -
  obtain mode abytes c1 where ea:
    "encode_address c a (src_len + tgt_pos) = (mode, abytes, c1)"
    by (cases "encode_address c a (src_len + tgt_pos)") auto
  obtain op needs_sz where fop:
    "find_single_copy_opcode n mode = (op, needs_sz)"
    by (cases "find_single_copy_opcode n mode") auto
  have abytes_le: "length abytes \<le> 5"
    by (rule encode_address_length_le_5[OF ea a_bd])
  show "data' = data"
    using eo ea fop by (auto simp: Let_def)
  show "length addr' \<le> length addr + 5"
    using eo ea fop abytes_le by (auto simp: Let_def)
  show "tgt_pos' = tgt_pos + n"
    using eo ea fop by (auto simp: Let_def)
  show "length inst' \<le> length inst + 1 + varint_size n"
    using eo ea fop by (cases needs_sz) (auto simp: Let_def)
  show "4 \<le> n \<Longrightarrow> n \<le> 18 \<Longrightarrow> length inst' = length inst + 1"
  proof -
    assume n_range: "4 \<le> n" "n \<le> 18"
    have no_sz: "needs_sz = False"
      using fop n_range
      by (auto simp: find_single_copy_opcode_def Let_def split: if_splits)
    show "length inst' = length inst + 1"
      using eo ea fop no_sz by (auto simp: Let_def)
  qed
qed

(* ---------- Lifting to the stateful emit wrappers ---------- *)

lemma emit_inst_spec_fields:
  assumes eo: "encode_one i src_len (enc_flushed st) (enc_cache st)
                 (enc_data st) (enc_inst st) (enc_addr st)
               = (data', inst', addr', c', fl')"
  shows "emit_inst_spec src_len i st
           = st \<lparr> enc_data := data', enc_inst := inst', enc_addr := addr'
                , enc_cache := c', enc_flushed := fl'
                , enc_trace := enc_trace st @ [i] \<rparr>"
  using eo by (simp add: emit_inst_spec_def)

lemma emit_inst_spec_flush_ok_bounded:
  assumes bounded: "enc_sections_bounded st"
      and ok: "flush_inst_ok i"
  shows "enc_sections_bounded (emit_inst_spec src_len i st)"
proof -
  from ok consider
      (Add) bs where "i = RAdd bs" "bs \<noteq> []"
    | (Run) b n where "i = RRun b n" "min_run \<le> n"
    by (auto simp: flush_inst_ok_def)
  then show ?thesis
  proof cases
    case (Add bs)
    obtain data' inst' addr' c' fl' where eo:
      "encode_one (RAdd bs) src_len (enc_flushed st) (enc_cache st)
         (enc_data st) (enc_inst st) (enc_addr st)
       = (data', inst', addr', c', fl')"
      by (cases "encode_one (RAdd bs) src_len (enc_flushed st) (enc_cache st)
                   (enc_data st) (enc_inst st) (enc_addr st)") auto
    note g = encode_one_add_growth[OF eo Add(2)]
    note res = emit_inst_spec_fields[OF eo]
    show ?thesis
      apply (rule enc_sections_bounded_step[OF bounded,
               where kd = "length bs" and ki = "length bs"
                 and ka = 0 and kf = "length bs"])
      subgoal using res g(1) Add(1) by simp
      subgoal using res g(2) Add(1) by simp
      subgoal using res g(3) Add(1) by simp
      subgoal using res g(4) Add(1) by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by simp
      done
  next
    case (Run b n)
    obtain data' inst' addr' c' fl' where eo:
      "encode_one (RRun b n) src_len (enc_flushed st) (enc_cache st)
         (enc_data st) (enc_inst st) (enc_addr st)
       = (data', inst', addr', c', fl')"
      by (cases "encode_one (RRun b n) src_len (enc_flushed st) (enc_cache st)
                   (enc_data st) (enc_inst st) (enc_addr st)") auto
    note g = encode_one_run_growth[OF eo Run(2)]
    note res = emit_inst_spec_fields[OF eo]
    have n4: "4 \<le> n" using Run(2) by (simp add: min_run_def)
    show ?thesis
      apply (rule enc_sections_bounded_step[OF bounded,
               where kd = 1 and ki = n and ka = 0 and kf = n])
      subgoal using res g(1) Run(1) by simp
      subgoal using res g(2) Run(1) by simp
      subgoal using res g(3) Run(1) by simp
      subgoal using res g(4) Run(1) by simp
      subgoal using n4 by linarith
      subgoal by simp
      subgoal by simp
      subgoal using n4 by linarith
      done
  qed
qed

lemma emit_insts_spec_flush_ok_bounded:
  assumes bounded: "enc_sections_bounded st"
      and ok: "\<forall>i \<in> set insts. flush_inst_ok i"
  shows "enc_sections_bounded (emit_insts_spec src_len insts st)"
  using bounded ok
proof (induction insts arbitrary: st)
  case Nil
  then show ?case by (simp add: emit_insts_spec_def)
next
  case (Cons i insts)
  have step: "enc_sections_bounded (emit_inst_spec src_len i st)"
    by (rule emit_inst_spec_flush_ok_bounded[OF Cons.prems(1)])
       (use Cons.prems(2) in simp)
  have unfold_cons:
    "emit_insts_spec src_len (i # insts) st
       = emit_insts_spec src_len insts (emit_inst_spec src_len i st)"
    by (simp add: emit_insts_spec_def)
  show ?case
    using Cons.IH[OF step] Cons.prems(2) unfold_cons by simp
qed

lemma flush_pending_spec_sections_bounded:
  assumes bounded: "enc_sections_bounded st"
  shows "enc_sections_bounded (flush_pending_spec src_len st)"
proof -
  have inner: "enc_sections_bounded
                 (emit_insts_spec src_len (flush_pending_insts (enc_pending st)) st)"
    by (rule emit_insts_spec_flush_ok_bounded[OF bounded flush_pending_insts_shape])
  then show ?thesis
    by (simp add: flush_pending_spec_def enc_sections_bounded_def)
qed

(* ---------- Copy emission ---------- *)

lemma emit_copy_spec_growth:
  assumes a_bd: "a < 2 ^ 32"
  shows "enc_data (emit_copy_spec sl a l st) = enc_data st"
    and "length (enc_inst (emit_copy_spec sl a l st))
           \<le> length (enc_inst st) + 1 + varint_size l"
    and "4 \<le> l \<Longrightarrow> l \<le> 18 \<Longrightarrow>
           length (enc_inst (emit_copy_spec sl a l st)) = length (enc_inst st) + 1"
    and "length (enc_addr (emit_copy_spec sl a l st)) \<le> length (enc_addr st) + 5"
    and "enc_flushed (emit_copy_spec sl a l st) = enc_flushed st + l"
proof -
  obtain data' inst' addr' c' fl' where eo:
    "encode_one (RCopy a l) sl (enc_flushed st) (enc_cache st)
       (enc_data st) (enc_inst st) (enc_addr st)
     = (data', inst', addr', c', fl')"
    by (cases "encode_one (RCopy a l) sl (enc_flushed st) (enc_cache st)
                 (enc_data st) (enc_inst st) (enc_addr st)") auto
  note g = encode_one_copy_growth[OF eo a_bd]
  have res: "emit_copy_spec sl a l st
     = (st \<lparr> enc_data := data', enc_inst := inst', enc_addr := addr'
           , enc_cache := c', enc_flushed := fl'
           , enc_trace := enc_trace st @ [RCopy a l] \<rparr>)
         \<lparr> enc_tp := enc_tp st + l \<rparr>"
    using emit_inst_spec_fields[OF eo] by (simp add: emit_copy_spec_def)
  show "enc_data (emit_copy_spec sl a l st) = enc_data st"
    using res g(1) by simp
  show "length (enc_inst (emit_copy_spec sl a l st))
          \<le> length (enc_inst st) + 1 + varint_size l"
    using res g(2) by simp
  show "4 \<le> l \<Longrightarrow> l \<le> 18 \<Longrightarrow>
          length (enc_inst (emit_copy_spec sl a l st)) = length (enc_inst st) + 1"
    using res g(3) by simp
  show "length (enc_addr (emit_copy_spec sl a l st)) \<le> length (enc_addr st) + 5"
    using res g(4) by simp
  show "enc_flushed (emit_copy_spec sl a l st) = enc_flushed st + l"
    using res g(5) by simp
qed

lemma emit_copy_spec_sections_bounded:
  assumes bounded: "enc_sections_bounded st"
      and l4: "4 \<le> l"
      and a_bd: "a < 2 ^ 32"
  shows "enc_sections_bounded (emit_copy_spec sl a l st)"
proof (cases "l \<le> 18")
  case True
  note g = emit_copy_spec_growth[OF a_bd, where sl = sl and l = l and st = st]
  show ?thesis
    apply (rule enc_sections_bounded_step[OF bounded,
             where kd = 0 and ki = 1 and ka = 5 and kf = l])
    subgoal using g(1) by simp
    subgoal using g(3)[OF l4 True] by simp
    subgoal using g(4) by simp
    subgoal using g(5) by simp
    subgoal by simp
    subgoal using l4 by linarith
    subgoal using l4 by linarith
    subgoal using l4 by linarith
    done
next
  case False
  hence l19: "19 \<le> l" by simp
  have vs: "varint_size l < l"
    using varint_size_lt_self[of l] l19 by simp
  note g = emit_copy_spec_growth[OF a_bd, where sl = sl and l = l and st = st]
  show ?thesis
    apply (rule enc_sections_bounded_step[OF bounded,
             where kd = 0 and ki = "1 + varint_size l" and ka = 5 and kf = l])
    subgoal using g(1) by simp
    subgoal using g(2) by simp
    subgoal using g(4) by simp
    subgoal using g(5) by simp
    subgoal by simp
    subgoal using vs by linarith
    subgoal using l4 by linarith
    subgoal using vs l19 by linarith
    done
qed

lemma flush_then_emit_copy_spec_sections_bounded:
  assumes bounded: "enc_sections_bounded st"
      and l4: "4 \<le> l"
      and a_bd: "a < 2 ^ 32"
  shows "enc_sections_bounded (flush_then_emit_copy_spec sl a l st)"
proof -
  have bounded0:
    "enc_sections_bounded (if enc_pending st = [] then st
                           else flush_pending_spec sl st)"
    using bounded flush_pending_spec_sections_bounded[OF bounded] by simp
  show ?thesis
    using emit_copy_spec_sections_bounded[OF bounded0 l4 a_bd]
    by (simp add: flush_then_emit_copy_spec_def Let_def)
qed

(* ---------- Fused ADD+COPY emission ---------- *)

lemma fused_copy_len_spec_ge_4:
  assumes "fused_copy_len_spec mode l = Some csz"
  shows "4 \<le> csz"
  using assms
  by (auto simp: fused_copy_len_spec_def min_match_def min_def split: if_splits)

(* A remainder copy only arises from the (min l 6) branch, so the fused
   part consumed exactly 6 bytes. This exact value is essential: the
   4*addr <= 5*flushed conjunct holds with equality in that case. *)
lemma fused_copy_len_spec_lt_imp_6:
  assumes "fused_copy_len_spec mode l = Some csz"
      and "csz < l"
  shows "csz = 6"
  using assms
  by (auto simp: fused_copy_len_spec_def min_def split: if_splits)

lemma try_emit_add_copy_spec_growthE:
  assumes some: "try_emit_add_copy_spec sl a l st = Some st'"
      and a_bd: "a < 2 ^ 32"
  obtains csz where
    "length (enc_data st') = length (enc_data st) + length (enc_pending st)"
    "length (enc_inst st') = length (enc_inst st) + 1"
    "length (enc_addr st') \<le> length (enc_addr st) + 5"
    "enc_flushed st' = enc_flushed st + length (enc_pending st) + csz"
    "enc_tp st' = enc_tp st + csz"
    "4 \<le> csz"
    "csz < l \<Longrightarrow> csz = 6"
    "1 \<le> length (enc_pending st)"
proof -
  obtain mode abytes cache' where ea:
    "encode_address (enc_cache st) a (sl + enc_tp st) = (mode, abytes, cache')"
    by (cases "encode_address (enc_cache st) a (sl + enc_tp st)") auto
  from some ea obtain csz op where
      pend1: "1 \<le> length (enc_pending st)"
      and fused: "fused_copy_len_spec mode l = Some csz"
      and st'_eq:
        "st' =
          st \<lparr> enc_tp := enc_tp st + csz
             , enc_flushed := enc_flushed st + length (enc_pending st) + csz
             , enc_pending := []
             , enc_data := enc_data st @ enc_pending st
             , enc_inst := enc_inst st @ [word_of_nat op]
             , enc_addr := enc_addr st @ abytes
             , enc_cache := cache'
             , enc_trace := enc_trace st
                 @ [RAdd (enc_pending st), RCopy a csz] \<rparr>"
    by (auto simp: try_emit_add_copy_spec_def Let_def
             split: option.splits if_splits)
  have abytes_le: "length abytes \<le> 5"
    by (rule encode_address_length_le_5[OF ea a_bd])
  show ?thesis
  proof (rule that)
    show "length (enc_data st') = length (enc_data st) + length (enc_pending st)"
      using st'_eq by simp
    show "length (enc_inst st') = length (enc_inst st) + 1"
      using st'_eq by simp
    show "length (enc_addr st') \<le> length (enc_addr st) + 5"
      using st'_eq abytes_le by simp
    show "enc_flushed st' = enc_flushed st + length (enc_pending st) + csz"
      using st'_eq by simp
    show "enc_tp st' = enc_tp st + csz"
      using st'_eq by simp
    show "4 \<le> csz"
      by (rule fused_copy_len_spec_ge_4[OF fused])
    show "csz < l \<Longrightarrow> csz = 6"
      using fused_copy_len_spec_lt_imp_6[OF fused] by simp
    show "1 \<le> length (enc_pending st)"
      by (rule pend1)
  qed
qed

(* ---------- Step preservation ---------- *)

lemma encode_window_full_step_sections_bounded:
  assumes bounded: "enc_sections_bounded st"
      and index: "index = build_index_spec src"
      and src_bd: "length src < 2 ^ 32"
  shows "enc_sections_bounded (encode_window_full_step src tgt index st)"
proof -
  let ?m = "find_best_match_spec src tgt (enc_tp st) index"
  show ?thesis
  proof (cases "em_len ?m < min_match")
    case True
    then have "encode_window_full_step src tgt index st
                 = buffer_pending_byte_spec (tgt ! enc_tp st) st"
      by (simp add: encode_window_full_step_def Let_def)
    then show ?thesis using bounded by simp
  next
    case False
    note match_branch = False
    hence match_min: "min_match \<le> em_len ?m" by simp
    have m_def: "?m = find_best_match_spec src tgt (enc_tp st) (build_index_spec src)"
      using index by simp
    have sound:
      "em_pos ?m + em_len ?m \<le> length src
       \<and> enc_tp st + em_len ?m \<le> length tgt
       \<and> (\<forall>k < em_len ?m. src ! (em_pos ?m + k) = tgt ! (enc_tp st + k))"
      by (rule find_best_match_spec_sound[OF m_def match_min])
    have sound1: "em_pos ?m + em_len ?m \<le> length src"
      using sound by blast
    have pos_bd: "em_pos ?m < 2 ^ 32"
      using sound1 src_bd by linarith
    have len4: "4 \<le> em_len ?m"
      using match_min by (simp add: min_match_def)
    show ?thesis
    proof (cases "try_emit_add_copy_spec (length src) (em_pos ?m) (em_len ?m) st")
      case None
      then have step_eq: "encode_window_full_step src tgt index st
        = flush_then_emit_copy_spec (length src) (em_pos ?m) (em_len ?m) st"
        using match_branch by (simp add: encode_window_full_step_def Let_def)
      show ?thesis
        unfolding step_eq
        by (rule flush_then_emit_copy_spec_sections_bounded[OF bounded len4 pos_bd])
    next
      case (Some fused)
      from try_emit_add_copy_spec_growthE[OF Some pos_bd] obtain csz where
        gd: "length (enc_data fused) = length (enc_data st) + length (enc_pending st)"
        and gi: "length (enc_inst fused) = length (enc_inst st) + 1"
        and ga: "length (enc_addr fused) \<le> length (enc_addr st) + 5"
        and gf: "enc_flushed fused
                   = enc_flushed st + length (enc_pending st) + csz"
        and gtp: "enc_tp fused = enc_tp st + csz"
        and csz4: "4 \<le> csz"
        and csz6: "csz < em_len ?m \<Longrightarrow> csz = 6"
        and pend1: "1 \<le> length (enc_pending st)"
        by blast
      have consumed_eq: "enc_tp fused - enc_tp st = csz"
        using gtp by simp
      show ?thesis
      proof (cases "enc_tp fused - enc_tp st < em_len ?m")
        case False
        then have step_eq: "encode_window_full_step src tgt index st = fused"
          using Some match_branch
          by (simp add: encode_window_full_step_def Let_def)
        show ?thesis
          unfolding step_eq
          apply (rule enc_sections_bounded_step[OF bounded,
                   where kd = "length (enc_pending st)" and ki = 1 and ka = 5
                     and kf = "length (enc_pending st) + csz"])
          subgoal using gd by simp
          subgoal using gi by simp
          subgoal using ga by simp
          subgoal using gf by simp
          subgoal by simp
          subgoal using csz4 by linarith
          subgoal using csz4 by (simp add: add_mult_distrib2)
          subgoal using csz4 pend1 by (simp add: add_mult_distrib2; linarith?)
          done
      next
        case True
        have csz_lt: "csz < em_len ?m"
          using True consumed_eq by simp
        have csz_eq: "csz = 6"
          by (rule csz6[OF csz_lt])
        have step_eq: "encode_window_full_step src tgt index st
          = emit_copy_spec (length src) (em_pos ?m + csz) (em_len ?m - csz) fused"
          using Some match_branch True consumed_eq
          by (simp add: encode_window_full_step_def Let_def)
        have rest1: "1 \<le> em_len ?m - csz"
          using csz_lt by simp
        have addr2_bd: "em_pos ?m + csz < 2 ^ 32"
          using sound1 csz_lt src_bd by linarith
        have vs: "varint_size (em_len ?m - csz) \<le> em_len ?m - csz"
          by (rule varint_size_le_self[OF rest1])
        note cg = emit_copy_spec_growth[OF addr2_bd,
                    where sl = "length src" and l = "em_len ?m - csz" and st = fused]
        show ?thesis
          unfolding step_eq
          apply (rule enc_sections_bounded_step[OF bounded,
                   where kd = "length (enc_pending st)"
                     and ki = "2 + varint_size (em_len ?m - csz)"
                     and ka = 10
                     and kf = "length (enc_pending st) + 6 + (em_len ?m - csz)"])
          subgoal using cg(1) gd by simp
          subgoal using cg(2) gi by linarith
          subgoal using cg(4) ga by linarith
          subgoal using cg(5) gf csz_eq by simp
          subgoal by simp
          subgoal using vs by linarith
          subgoal using pend1 rest1 by (simp add: add_mult_distrib2; linarith?)
          subgoal using vs pend1 rest1 by (simp add: add_mult_distrib2; linarith?)
          done
      qed
    qed
  qed
qed

(* ---------- Loop preservation and final-state bounds ---------- *)

lemma encode_window_full_loop_sections_bounded:
  assumes bounded: "enc_sections_bounded st"
      and index: "index = build_index_spec src"
      and src_bd: "length src < 2 ^ 32"
  shows "enc_sections_bounded (encode_window_full_loop fuel src tgt index st)"
  using bounded
proof (induction fuel arbitrary: st)
  case 0
  then show ?case
    by (auto intro: flush_pending_spec_sections_bounded)
next
  case (Suc fuel)
  show ?case
  proof (cases "length tgt \<le> enc_tp st")
    case True
    then show ?thesis
      using flush_pending_spec_sections_bounded[OF Suc.prems]
      by (simp add: encode_window_full_loop_Suc
               del: encode_window_full_loop.simps)
  next
    case False
    have step: "enc_sections_bounded (encode_window_full_step src tgt index st)"
      by (rule encode_window_full_step_sections_bounded[OF Suc.prems index src_bd])
    then show ?thesis
      using False Suc.IH[OF step]
      by (simp add: encode_window_full_loop_Suc
               del: encode_window_full_loop.simps)
  qed
qed

(* Bounds on the final loop state itself. This is the exact term used by
   the C-side caps predicate `encoder_final_section_caps_ok` (via
   `encode_window_final_spec_state` in VcdiffEnc_Serialize). *)
theorem encode_window_final_state_section_bounds:
  fixes src tgt :: "byte list"
  assumes src_bd: "length src < 2 ^ 32"
  defines "fin \<equiv> encode_window_full_loop (length tgt + 1) src tgt
                   (build_index_spec src) enc_full_init"
  shows "length (enc_data fin) \<le> length tgt"
    and "length (enc_inst fin) \<le> length tgt"
    and "4 * length (enc_addr fin) \<le> 5 * length tgt"
    and "length (enc_data fin) + length (enc_inst fin) + length (enc_addr fin)
           \<le> 2 * length tgt"
proof -
  have bounded: "enc_sections_bounded fin"
    unfolding fin_def
    by (rule encode_window_full_loop_sections_bounded
         [OF enc_sections_bounded_init refl src_bd])
  have fuel: "length tgt - enc_tp enc_full_init < length tgt + 1"
    by (simp add: enc_full_init_def)
  have flushed: "enc_flushed fin = length tgt"
    using encode_window_full_loop_trace_complete
            [OF encode_window_full_trace_inv_init refl fuel]
    by (simp add: fin_def Let_def)
  note b = enc_sections_boundedD[OF bounded]
  show "length (enc_data fin) \<le> length tgt"
    using b(1) flushed by simp
  show "length (enc_inst fin) \<le> length tgt"
    using b(2) flushed by simp
  show "4 * length (enc_addr fin) \<le> 5 * length tgt"
    using b(3) flushed by simp
  show "length (enc_data fin) + length (enc_inst fin) + length (enc_addr fin)
          \<le> 2 * length tgt"
    using b(4) flushed by simp
qed

theorem encode_window_full_spec_section_bounds:
  assumes src_bd: "length src < 2 ^ 32"
  shows "length (efr_data (encode_window_full_spec src tgt)) \<le> length tgt"
    and "length (efr_inst (encode_window_full_spec src tgt)) \<le> length tgt"
    and "4 * length (efr_addr (encode_window_full_spec src tgt)) \<le> 5 * length tgt"
    and "length (efr_data (encode_window_full_spec src tgt))
           + length (efr_inst (encode_window_full_spec src tgt))
           + length (efr_addr (encode_window_full_spec src tgt))
         \<le> 2 * length tgt"
proof -
  define fin where
    "fin = encode_window_full_loop (length tgt + 1) src tgt
             (build_index_spec src) enc_full_init"
  note b = encode_window_final_state_section_bounds[OF src_bd, of tgt,
             folded fin_def]
  have proj:
    "efr_data (encode_window_full_spec src tgt) = enc_data fin"
    "efr_inst (encode_window_full_spec src tgt) = enc_inst fin"
    "efr_addr (encode_window_full_spec src tgt) = enc_addr fin"
    by (simp_all add: encode_window_full_spec_def fin_def Let_def
                      enc_full_result_of_state_def)
  show "length (efr_data (encode_window_full_spec src tgt)) \<le> length tgt"
    using b(1) proj(1) by simp
  show "length (efr_inst (encode_window_full_spec src tgt)) \<le> length tgt"
    using b(2) proj(2) by simp
  show "4 * length (efr_addr (encode_window_full_spec src tgt)) \<le> 5 * length tgt"
    using b(3) proj(3) by simp
  show "length (efr_data (encode_window_full_spec src tgt))
          + length (efr_inst (encode_window_full_spec src tgt))
          + length (efr_addr (encode_window_full_spec src tgt))
        \<le> 2 * length tgt"
    using b(4) proj by simp
qed

(* ---------- 32-bit fit and total output length ---------- *)

lemma pow31_nat: "(2::nat) ^ 31 = 2147483648"
  by simp

lemma pow32_nat: "(2::nat) ^ 32 = 4294967296"
  by simp

theorem encode_window_full_spec_fits_32:
  assumes src_bd: "length src < 2 ^ 32"
      and tgt_bd: "length tgt < 2 ^ 31 - 32"
  shows "sections_fit_32 src tgt (encode_window_full_spec src tgt)"
proof -
  let ?r = "encode_window_full_spec src tgt"
  note b = encode_window_full_spec_section_bounds[OF src_bd, of tgt]
  have tgt32: "length tgt < 2 ^ 32"
    using tgt_bd pow31_nat pow32_nat by linarith
  have d32: "length (efr_data ?r) < 2 ^ 32"
    using b(1) tgt32 by linarith
  have i32: "length (efr_inst ?r) < 2 ^ 32"
    using b(2) tgt32 by linarith
  have a32: "length (efr_addr ?r) < 2 ^ 32"
    using b(3) tgt_bd pow31_nat pow32_nat by linarith
  have vs_tgt: "varint_size (length tgt) \<le> 5"
    by (rule varint_size_le_5_32[OF tgt32])
  have vs_d: "varint_size (length (efr_data ?r)) \<le> 5"
    by (rule varint_size_le_5_32[OF d32])
  have vs_i: "varint_size (length (efr_inst ?r)) \<le> 5"
    by (rule varint_size_le_5_32[OF i32])
  have vs_a: "varint_size (length (efr_addr ?r)) \<le> 5"
    by (rule varint_size_le_5_32[OF a32])
  have dlen32:
    "varint_size (length tgt) + 1
       + varint_size (length (efr_data ?r))
       + varint_size (length (efr_inst ?r))
       + varint_size (length (efr_addr ?r))
       + length (efr_data ?r) + length (efr_inst ?r) + length (efr_addr ?r)
     < 2 ^ 32"
    using vs_tgt vs_d vs_i vs_a b(4) tgt_bd pow31_nat pow32_nat by linarith
  show ?thesis
    using d32 i32 a32 dlen32 by (simp add: sections_fit_32_def)
qed

lemma serialize_length_le:
  assumes src32: "length src < 2 ^ 32"
      and d32: "length data < 2 ^ 32"
      and i32: "length inst < 2 ^ 32"
      and a32: "length addr < 2 ^ 32"
      and tgt32: "length tgt < 2 ^ 32"
      and dlen32: "varint_size (length tgt) + 1
             + varint_size (length data) + varint_size (length inst)
             + varint_size (length addr)
             + length data + length inst + length addr < 2 ^ 32"
  shows "length (serialize src tgt data inst addr)
           \<le> 38 + length data + length inst + length addr"
proof -
  have vs_src: "varint_size (length src) \<le> 5"
    by (rule varint_size_le_5_32[OF src32])
  have vs_tgt: "varint_size (length tgt) \<le> 5"
    by (rule varint_size_le_5_32[OF tgt32])
  have vs_d: "varint_size (length data) \<le> 5"
    by (rule varint_size_le_5_32[OF d32])
  have vs_i: "varint_size (length inst) \<le> 5"
    by (rule varint_size_le_5_32[OF i32])
  have vs_a: "varint_size (length addr) \<le> 5"
    by (rule varint_size_le_5_32[OF a32])
  have vs_dlen: "varint_size
      (varint_size (length tgt) + 1
       + varint_size (length data) + varint_size (length inst)
       + varint_size (length addr)
       + length data + length inst + length addr) \<le> 5"
    by (rule varint_size_le_5_32[OF dlen32])
  show ?thesis
    using vs_src vs_tgt vs_d vs_i vs_a vs_dlen
    by (simp add: serialize_def Let_def magic_bytes_def; linarith)
qed

theorem encode_spec_length_le:
  assumes src_bd: "length src < 2 ^ 32"
      and tgt_bd: "length tgt < 2 ^ 31 - 32"
  shows "length (encode_spec src tgt) \<le> 2 * length tgt + 38"
proof -
  let ?r = "encode_window_full_spec src tgt"
  note b = encode_window_full_spec_section_bounds[OF src_bd, of tgt]
  have fit: "sections_fit_32 src tgt ?r"
    by (rule encode_window_full_spec_fits_32[OF src_bd tgt_bd])
  have enc_eq: "encode_spec src tgt
     = serialize src tgt (efr_data ?r) (efr_inst ?r) (efr_addr ?r)"
    using fit by (simp add: encode_spec_def encode_spec_full_def Let_def)
  have tgt32: "length tgt < 2 ^ 32"
    using tgt_bd pow31_nat pow32_nat by linarith
  have d32: "length (efr_data ?r) < 2 ^ 32"
    and i32: "length (efr_inst ?r) < 2 ^ 32"
    and a32: "length (efr_addr ?r) < 2 ^ 32"
    and dlen32: "varint_size (length tgt) + 1
       + varint_size (length (efr_data ?r))
       + varint_size (length (efr_inst ?r))
       + varint_size (length (efr_addr ?r))
       + length (efr_data ?r) + length (efr_inst ?r) + length (efr_addr ?r)
     < 2 ^ 32"
    using fit by (simp_all add: sections_fit_32_def)
  have ser_le: "length (serialize src tgt (efr_data ?r) (efr_inst ?r) (efr_addr ?r))
    \<le> 38 + length (efr_data ?r) + length (efr_inst ?r) + length (efr_addr ?r)"
    by (rule serialize_length_le[OF src_bd d32 i32 a32 tgt32 dlen32])
  have len_eq: "length (encode_spec src tgt)
     = length (serialize src tgt (efr_data ?r) (efr_inst ?r) (efr_addr ?r))"
    using enc_eq by simp
  show ?thesis
    using len_eq ser_le b(4) by linarith
qed

corollary encode_spec_length_lt_2p32:
  assumes src_bd: "length src < 2 ^ 32"
      and tgt_bd: "length tgt < 2 ^ 31 - 32"
  shows "length (encode_spec src tgt) < 2 ^ 32"
  using encode_spec_length_le[OF assms] tgt_bd pow31_nat pow32_nat by linarith

(* ---------- Caller-checkable capacity envelope ---------- *)

(*
  The exact arithmetic envelope enforced by the C entrypoint's upfront
  check (vcdiff_enc.c). A caller meeting it is guaranteed a successful
  encode: the section bounds above show no internal overflow can occur.

  The addr conjunct uses the division form the C can compute in 32 bits;
  it implies the tight 4*addr_cap >= 5*tgt_len bound (and tgt_len + 64
  <= addr_cap, required by the window-loop budget invariant).
*)
definition encoder_bounds_ok ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "encoder_bounds_ok out_cap src_len tgt_len pending_cap
      data_cap inst_cap addr_cap \<longleftrightarrow>
     tgt_len < 2 ^ 31 - 32 \<and>
     src_len < 2 ^ 32 - 1 \<and>
     src_len + tgt_len < 2 ^ 32 \<and>
     tgt_len \<le> pending_cap \<and>
     tgt_len + 64 \<le> data_cap \<and>
     tgt_len + 64 \<le> inst_cap \<and>
     tgt_len + tgt_len div 4 + 64 \<le> addr_cap \<and>
     2 * tgt_len + 38 \<le> out_cap"

lemma encoder_bounds_ok_addr_arith:
  assumes ok: "encoder_bounds_ok out_cap src_len tgt_len pending_cap
                 data_cap inst_cap addr_cap"
  shows "5 * tgt_len \<le> 4 * addr_cap"
    and "tgt_len + 64 \<le> addr_cap"
proof -
  have acap: "tgt_len + tgt_len div 4 + 64 \<le> addr_cap"
    using ok by (simp add: encoder_bounds_ok_def)
  have division: "4 * (tgt_len div 4) + tgt_len mod 4 = tgt_len"
    by simp
  have mod_lt: "tgt_len mod 4 < 4"
    by simp
  show "5 * tgt_len \<le> 4 * addr_cap"
    using acap division mod_lt by linarith
  show "tgt_len + 64 \<le> addr_cap"
    using acap by linarith
qed

lemma encoder_bounds_ok_out_cap:
  assumes ok: "encoder_bounds_ok out_cap (length src) (length tgt) pending_cap
                 data_cap inst_cap addr_cap"
  shows "length (encode_spec src tgt) \<le> out_cap"
proof -
  have src_bd': "length src < 2 ^ 32 - 1"
    using ok by (simp add: encoder_bounds_ok_def)
  have src_bd: "length src < 2 ^ 32"
    using src_bd' pow32_nat by linarith
  have tgt_bd: "length tgt < 2 ^ 31 - 32"
    using ok by (simp add: encoder_bounds_ok_def)
  have "length (encode_spec src tgt) \<le> 2 * length tgt + 38"
    by (rule encode_spec_length_le[OF src_bd tgt_bd])
  moreover have "2 * length tgt + 38 \<le> out_cap"
    using ok by (simp add: encoder_bounds_ok_def)
  ultimately show ?thesis by linarith
qed

(* The encoder never emits an empty patch: serialize always begins with
   the 4-byte magic. Distinguishes success (n > 0) from the 0 reject. *)
lemma serialize_nonempty:
  "serialize src tgt data inst addr \<noteq> []"
  by (simp add: serialize_def Let_def magic_bytes_def)

lemma encode_spec_length_pos:
  "0 < length (encode_spec src tgt)"
  by (auto simp: encode_spec_def encode_spec_full_def encode_spec_run_def
                 serialize_from_insts_def Let_def serialize_nonempty)

end
