(*
  VCDIFF default code table (RFC 3284 §5.4).

  The 256-entry table maps opcodes to pairs of half-instructions (inst1,
  inst2). A half-instruction has a type (NOOP/ADD/RUN/COPY-with-mode) and
  either a literal size or 0 meaning "size follows as a varint in the
  instruction stream".

  Layout (from the C decoder's build_code_table):
    0           RUN   size=0                    / NOOP
    1           ADD   size=0                    / NOOP
    2..18       ADD   size=1..17                / NOOP
    19..162     COPY  mode=0..8, size=0,4..18   / NOOP
    163..234    ADD   size=1..4   mode 0..5     / COPY size=4..6 mode 0..5
    235..246    ADD   size=1..4   mode 6..8     / COPY size=4 mode 6..8
    247..255    COPY  size=4 mode=0..8          / ADD  size=1

  We mirror the *meaning* of the C table rather than its byte layout. The
  exhaustion lemmas below are what the encoder/decoder refinement uses —
  the payload of each opcode is a deterministic function of the opcode,
  and the encoder's opcode-selection functions (`find_single_*`,
  `find_add_copy_opcode`, `find_copy_add_opcode`) are left-inverses of
  `default_entry` on the in-range inputs.
*)
theory CodeTable
  imports Bytes
begin

(* ---------- Half-instructions ---------- *)

datatype inst_type = NOOP | IADD | IRUN | ICOPY nat   \<comment> \<open>mode 0..8 for COPY\<close>

record half_inst =
  ity  :: inst_type
  isz  :: nat   \<comment> \<open>0 = read varint\<close>

definition noop_hi :: half_inst where
  "noop_hi = \<lparr> ity = NOOP, isz = 0 \<rparr>"

definition add_hi :: "nat \<Rightarrow> half_inst" where
  "add_hi sz = \<lparr> ity = IADD, isz = sz \<rparr>"

definition run_hi :: "nat \<Rightarrow> half_inst" where
  "run_hi sz = \<lparr> ity = IRUN, isz = sz \<rparr>"

definition copy_hi :: "nat \<Rightarrow> nat \<Rightarrow> half_inst" where
  "copy_hi sz mode = \<lparr> ity = ICOPY mode, isz = sz \<rparr>"

(* ---------- The default code table ---------- *)

(*
  Return the (inst1, inst2) pair for a given opcode (< 256). Decomposition
  into segments lets us reason about each regime separately.
*)
definition default_entry :: "nat \<Rightarrow> half_inst \<times> half_inst" where
  "default_entry op =
     (if op = 0 then (run_hi 0, noop_hi)
      else if op = 1 then (add_hi 0, noop_hi)
      else if op \<le> 18 then (add_hi (op - 1), noop_hi)
      else if op \<le> 162 then
        \<comment> \<open>Per-mode block of 16: first slot = size 0, then sizes 4..18.\<close>
        let rel = op - 19;
            mode = rel div 16;
            slot = rel mod 16
        in (copy_hi (if slot = 0 then 0 else slot + 3) mode, noop_hi)
      else if op \<le> 234 then
        \<comment> \<open>ADD(1..4) + COPY(4..6) modes 0..5, 12 entries per mode.\<close>
        let rel = op - 163;
            mode = rel div 12;
            r2 = rel mod 12;
            add_sz = (r2 div 3) + 1;
            copy_sz = (r2 mod 3) + 4
        in (add_hi add_sz, copy_hi copy_sz mode)
      else if op \<le> 246 then
        \<comment> \<open>ADD(1..4) + COPY(4) modes 6..8, 4 entries per mode.\<close>
        let rel = op - 235;
            mode = (rel div 4) + 6;
            add_sz = (rel mod 4) + 1
        in (add_hi add_sz, copy_hi 4 mode)
      else if op \<le> 255 then
        \<comment> \<open>COPY(4) + ADD(1) modes 0..8.\<close>
        let mode = op - 247
        in (copy_hi 4 mode, add_hi 1)
      else (noop_hi, noop_hi))"

(* ---------- Encoder's opcode selectors ---------- *)

(* Return (opcode, needs_size_varint) for a standalone ADD. *)
definition find_single_add_opcode :: "nat \<Rightarrow> nat \<times> bool" where
  "find_single_add_opcode sz =
     (if 1 \<le> sz \<and> sz \<le> 17 then (1 + sz, False)
      else (1, True))"

(* Return (opcode, needs_size_varint) for a standalone COPY of a given
   mode. The per-mode base is 19 + mode*16. *)
definition find_single_copy_opcode :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> bool" where
  "find_single_copy_opcode sz mode =
     (let base = 19 + mode * 16 in
      if 4 \<le> sz \<and> sz \<le> 18 then (base + sz - 3, False)
      else (base, True))"

(* Standalone RUN always uses opcode 0 with size varint. *)
definition find_single_run_opcode :: "nat \<Rightarrow> nat \<times> bool" where
  "find_single_run_opcode _ = (0, True)"

(* Try to fuse ADD(add_sz)+COPY(copy_sz,mode) into a single opcode. *)
definition find_add_copy_opcode :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_add_copy_opcode add_sz copy_sz mode =
     (if 1 \<le> add_sz \<and> add_sz \<le> 4 then
        if mode \<le> 5 \<and> 4 \<le> copy_sz \<and> copy_sz \<le> 6 then
          Some (163 + mode * 12 + (add_sz - 1) * 3 + (copy_sz - 4))
        else if 6 \<le> mode \<and> mode \<le> 8 \<and> copy_sz = 4 then
          Some (235 + (mode - 6) * 4 + (add_sz - 1))
        else None
      else None)"

(* Try to fuse COPY(copy_sz,mode)+ADD(add_sz) into a single opcode. *)
definition find_copy_add_opcode :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_copy_add_opcode copy_sz mode add_sz =
     (if copy_sz = 4 \<and> add_sz = 1 \<and> mode \<le> 8 then Some (247 + mode)
      else None)"

(* ---------- Exhaustion lemmas (Phase A.3 goals) ---------- *)

lemma default_entry_run_zero:
  "default_entry 0 = (run_hi 0, noop_hi)"
  by (simp add: default_entry_def)

lemma default_entry_add_varint:
  "default_entry 1 = (add_hi 0, noop_hi)"
  by (simp add: default_entry_def)

lemma default_entry_add_small:
  assumes "1 \<le> sz" "sz \<le> 17"
  shows   "default_entry (1 + sz) = (add_hi sz, noop_hi)"
  using assms by (simp add: default_entry_def)

lemma default_entry_copy_varint:
  assumes "mode \<le> 8"
  shows   "default_entry (19 + mode * 16) = (copy_hi 0 mode, noop_hi)"
proof -
  have op_ub: "19 + mode * 16 \<le> 162" using assms by simp
  have div_eq: "(mode * 16) div 16 = mode" by simp
  have mod_eq: "(mode * 16) mod 16 = 0" by simp
  show ?thesis
    using op_ub div_eq mod_eq
    by (simp add: default_entry_def Let_def)
qed

lemma default_entry_copy_small:
  assumes "mode \<le> 8" "4 \<le> sz" "sz \<le> 18"
  shows   "default_entry (19 + mode * 16 + sz - 3)
         = (copy_hi sz mode, noop_hi)"
proof -
  let ?op = "19 + mode * 16 + sz - 3"
  have sz_bds: "1 \<le> sz - 3" "sz - 3 \<le> 15" using assms by simp_all
  have key: "?op - 19 = mode * 16 + (sz - 3)" using assms(2) by simp
  have ub162: "?op \<le> 162" using assms by simp
  have op_gt_18: "?op > 18" using assms(2) by simp
  have slot_lt_16: "sz - 3 < 16" using sz_bds by linarith
  have div_eq: "(mode * 16 + (sz - 3)) div 16 = mode"
    using slot_lt_16 by simp
  have mod_eq: "(mode * 16 + (sz - 3)) mod 16 = sz - 3"
    using slot_lt_16 by simp
  have slot_ne_0: "sz - 3 \<noteq> 0" using sz_bds by simp
  have slot_plus_3: "(sz - 3) + 3 = sz" using assms(2) by simp
  show ?thesis
    using ub162 op_gt_18 div_eq mod_eq slot_ne_0 slot_plus_3 key
    by (simp add: default_entry_def Let_def)
qed

lemma default_entry_add_copy:
  assumes "1 \<le> add_sz" "add_sz \<le> 4"
          "((mode \<le> 5 \<and> 4 \<le> copy_sz \<and> copy_sz \<le> 6)
          \<or> (6 \<le> mode \<and> mode \<le> 8 \<and> copy_sz = 4))"
  shows "\<exists>op. find_add_copy_opcode add_sz copy_sz mode = Some op
           \<and> default_entry op = (add_hi add_sz, copy_hi copy_sz mode)"
proof (cases "mode \<le> 5 \<and> 4 \<le> copy_sz \<and> copy_sz \<le> 6")
  case True
  let ?op = "163 + mode * 12 + (add_sz - 1) * 3 + (copy_sz - 4)"
  have opcode: "find_add_copy_opcode add_sz copy_sz mode = Some ?op"
    using assms(1,2) True by (simp add: find_add_copy_opcode_def)
  have a_bd: "add_sz - 1 \<le> 3" using assms(2) by simp
  from True have c_bd: "copy_sz - 4 \<le> 2" by linarith
  have inner: "(add_sz - 1) * 3 + (copy_sz - 4) < 12"
    using a_bd c_bd by linarith
  have mode_bd: "mode \<le> 5" using True by simp
  have op_inner: "mode * 12 + ((add_sz - 1) * 3 + (copy_sz - 4)) \<le> 71"
    using mode_bd inner by linarith
  have ub234: "?op \<le> 234" using op_inner by simp
  have gt_162: "?op > 162" by simp
  have div_eq: "(mode * 12 + ((add_sz - 1) * 3 + (copy_sz - 4))) div 12 = mode"
    using inner by simp
  have mod_eq: "(mode * 12 + ((add_sz - 1) * 3 + (copy_sz - 4))) mod 12
                 = (add_sz - 1) * 3 + (copy_sz - 4)"
    using inner by simp
  have inner_div: "((add_sz - 1) * 3 + (copy_sz - 4)) div 3 = add_sz - 1"
    using c_bd by simp
  have inner_mod: "((add_sz - 1) * 3 + (copy_sz - 4)) mod 3 = copy_sz - 4"
    using c_bd by simp
  have add_sz_eq: "add_sz - 1 + 1 = add_sz" using assms(1) by simp
  have copy_sz_eq: "copy_sz - 4 + 4 = copy_sz" using True by simp
  have key: "?op - 163 = mode * 12 + ((add_sz - 1) * 3 + (copy_sz - 4))"
    by simp
  have entry: "default_entry ?op = (add_hi add_sz, copy_hi copy_sz mode)"
    using ub234 gt_162 div_eq mod_eq inner_div inner_mod add_sz_eq copy_sz_eq
    by (auto simp: default_entry_def Let_def key)
  show ?thesis using opcode entry by blast
next
  case False
  hence hi_mode: "6 \<le> mode \<and> mode \<le> 8 \<and> copy_sz = 4" using assms(3) by auto
  let ?op = "235 + (mode - 6) * 4 + (add_sz - 1)"
  have opcode: "find_add_copy_opcode add_sz copy_sz mode = Some ?op"
    using assms(1,2) hi_mode False
    by (auto simp: find_add_copy_opcode_def)
  have mode_minus: "mode - 6 \<le> 2" using hi_mode by linarith
  have a_bd: "add_sz - 1 \<le> 3" using assms(2) by linarith
  have lb: "?op \<ge> 235" by simp
  have ub: "?op \<le> 235 + 2 * 4 + 3" using mode_minus a_bd by linarith
  hence ub246: "?op \<le> 246" by simp
  have gt_234: "?op > 234" by simp
  have rel_eq: "?op - 235 = (mode - 6) * 4 + (add_sz - 1)" by simp
  have inner: "add_sz - 1 < 4" using a_bd by simp
  have div_eq: "((mode - 6) * 4 + (add_sz - 1)) div 4 = mode - 6"
    using inner by simp
  have mod_eq: "((mode - 6) * 4 + (add_sz - 1)) mod 4 = add_sz - 1"
    using inner by simp
  have mode_eq: "mode - 6 + 6 = mode" using hi_mode by simp
  have add_sz_eq: "add_sz - 1 + 1 = add_sz" using assms(1) by simp
  have entry: "default_entry ?op = (add_hi add_sz, copy_hi copy_sz mode)"
    using ub246 gt_234 div_eq mod_eq mode_eq add_sz_eq hi_mode
    by (auto simp: default_entry_def Let_def rel_eq)
  show ?thesis using opcode entry by blast
qed

lemma default_entry_copy_add:
  assumes "mode \<le> 8"
  shows "default_entry (247 + mode) = (copy_hi 4 mode, add_hi 1)"
proof -
  have lb: "247 + mode \<ge> 247" by simp
  have ub: "247 + mode \<le> 255" using assms by simp
  show ?thesis
    using lb ub by (simp add: default_entry_def)
qed

(* The encoder's find_single_add_opcode is a left inverse of default_entry
   on ADDs of size 1..17. *)
lemma find_single_add_opcode_roundtrip:
  assumes "1 \<le> sz" "sz \<le> 17"
  shows "find_single_add_opcode sz = (1 + sz, False)
       \<and> default_entry (1 + sz) = (add_hi sz, noop_hi)"
  using assms by (simp add: find_single_add_opcode_def default_entry_def)

end
