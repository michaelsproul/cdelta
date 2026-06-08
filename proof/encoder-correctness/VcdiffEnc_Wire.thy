theory VcdiffEnc_Wire
  imports
    VcdiffEnc_Writers
begin


(*
  Shared pure section-decoding predicates for the encoder proof.
  Encoder helper lemmas should preserve one of these predicates instead of
  depending on a concrete instruction-list serialization.
*)
definition section_decodes_prefix ::
  "byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
   cache \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> cache \<Rightarrow> bool" where
  "section_decodes_prefix src_seg tgt_len data inst addr c_in tgt_prefix target c_out \<longleftrightarrow>
     decode_loop (length inst) src_seg (length src_seg) tgt_len
       \<lparr> ds_data_rem = data
       , ds_inst_rem = inst
       , ds_addr_rem = addr
       , ds_cache = c_in
       , ds_tgt = tgt_prefix \<rparr>
     = Inl \<lparr> ds_data_rem = []
           , ds_inst_rem = []
           , ds_addr_rem = []
           , ds_cache = c_out
           , ds_tgt = target \<rparr>"

definition section_decodes ::
  "byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
   byte list \<Rightarrow> cache \<Rightarrow> bool" where
  "section_decodes src_seg tgt_len data inst addr target c_out \<longleftrightarrow>
     section_decodes_prefix src_seg tgt_len data inst addr cache_init [] target c_out"

definition dec_state_append ::
  "dec_state \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> dec_state" where
  "dec_state_append st data_tail inst_tail addr_tail =
     st \<lparr> ds_data_rem := ds_data_rem st @ data_tail
        , ds_inst_rem := ds_inst_rem st @ inst_tail
        , ds_addr_rem := ds_addr_rem st @ addr_tail \<rparr>"

definition add_inst_bytes :: "nat \<Rightarrow> byte list" where
  "add_inst_bytes n =
     (let (op, needs_sz) = find_single_add_opcode n in
      [word_of_nat op] @ (if needs_sz then varint_encode n else []))"

definition run_inst_bytes :: "nat \<Rightarrow> byte list" where
  "run_inst_bytes n =
     (let (op, needs_sz) = find_single_run_opcode n in
      [word_of_nat op] @ (if needs_sz then varint_encode n else []))"

definition copy_inst_bytes :: "nat \<Rightarrow> nat \<Rightarrow> byte list" where
  "copy_inst_bytes n mode =
     (let (op, needs_sz) = find_single_copy_opcode n mode in
      [word_of_nat op] @ (if needs_sz then varint_encode n else []))"

lemma section_decodesI:
  assumes "section_decodes_prefix src_seg tgt_len data inst addr cache_init [] target c_out"
  shows "section_decodes src_seg tgt_len data inst addr target c_out"
  using assms by (simp add: section_decodes_def)

lemma section_decodesD:
  assumes "section_decodes src_seg tgt_len data inst addr target c_out"
  shows "section_decodes_prefix src_seg tgt_len data inst addr cache_init [] target c_out"
  using assms by (simp add: section_decodes_def)

lemma pop_byte_append_success:
  assumes "pop_byte bs = Some (b, rest)"
  shows "pop_byte (bs @ tail) = Some (b, rest @ tail)"
  using assms by (cases bs) (simp_all add: pop_byte_def)

lemma varint_decode_loop_append_success:
  assumes "varint_decode_loop fuel acc bs = Some (v, rest)"
  shows "varint_decode_loop fuel acc (bs @ tail) = Some (v, rest @ tail)"
  using assms
proof (induction fuel arbitrary: acc bs rest)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis using Suc.prems by simp
  next
    case (Cons b bs')
    show ?thesis
    proof (cases "b AND 0x80 = 0")
      case True
      then show ?thesis
        using Suc.prems Cons by (simp add: Let_def split: if_splits)
    next
      case False
      let ?acc' = "acc * 128 + unat (b AND 0x7F)"
      have rec: "varint_decode_loop fuel ?acc' bs' = Some (v, rest)"
        using Suc.prems Cons False by (simp add: Let_def)
      have "varint_decode_loop fuel ?acc' (bs' @ tail) = Some (v, rest @ tail)"
        using Suc.IH[OF rec] .
      then show ?thesis
        using Cons False by (simp add: Let_def)
    qed
  qed
qed

lemma varint_decode_append_success:
  assumes "varint_decode bs = Some (v, rest)"
  shows "varint_decode (bs @ tail) = Some (v, rest @ tail)"
  using assms
  unfolding varint_decode_def
  by (rule varint_decode_loop_append_success)

lemma resolve_size_append_success:
  assumes "resolve_size h bs = Some (sz, rest)"
  shows "resolve_size h (bs @ tail) = Some (sz, rest @ tail)"
proof (cases "isz h = 0 \<and> ity h \<noteq> NOOP")
  case True
  then have "varint_decode bs = Some (sz, rest)"
    using assms by (simp add: resolve_size_def)
  then show ?thesis
    using True varint_decode_append_success[of bs sz rest tail]
    by (simp add: resolve_size_def)
next
  case False
  have literal: "Some (isz h, bs) = Some (sz, rest)"
    using assms False
    by (cases "isz h = 0"; cases "ity h = NOOP"; simp add: resolve_size_def)
  then have sz_eq: "sz = isz h" and rest_eq: "rest = bs"
    by simp_all
  then show ?thesis
    using False sz_eq rest_eq
    by (cases "isz h = 0"; cases "ity h = NOOP"; simp add: resolve_size_def)
qed

lemma decode_address_append_success:
  assumes "decode_address c mode here bs = Some (addr, rest, c')"
  shows "decode_address c mode here (bs @ tail) = Some (addr, rest @ tail, c')"
proof (cases "mode = 0")
  case True
  then obtain v r where
    dec: "varint_decode bs = Some (v, r)"
    and out: "addr = v" "rest = r" "c' = cache_update c v"
    using assms by (auto simp: decode_address_def split: option.splits prod.splits)
  have "varint_decode (bs @ tail) = Some (v, r @ tail)"
    by (rule varint_decode_append_success[OF dec])
  then show ?thesis
    using True out by (simp add: decode_address_def)
next
  case mode0: False
  show ?thesis
  proof (cases "mode = 1")
    case True
    then obtain v r where
      dec: "varint_decode bs = Some (v, r)"
      and v_ok: "\<not> here < v"
      and out: "addr = here - v" "rest = r" "c' = cache_update c (here - v)"
      using assms mode0
      by (auto simp: decode_address_def Let_def split: option.splits prod.splits if_splits)
    have "varint_decode (bs @ tail) = Some (v, r @ tail)"
      by (rule varint_decode_append_success[OF dec])
    then show ?thesis
      using True mode0 v_ok out by (simp add: decode_address_def Let_def)
  next
    case mode1: False
    show ?thesis
    proof (cases "mode < 2 + s_near")
      case True
      then obtain v r where
        dec: "varint_decode bs = Some (v, r)"
        and out:
          "addr = near c ! (mode - 2) + v"
          "rest = r"
          "c' = cache_update c (near c ! (mode - 2) + v)"
        using assms mode0 mode1
        by (auto simp: decode_address_def Let_def split: option.splits prod.splits if_splits)
      have "varint_decode (bs @ tail) = Some (v, r @ tail)"
        by (rule varint_decode_append_success[OF dec])
      then show ?thesis
        using True mode0 mode1 out by (simp add: decode_address_def Let_def)
    next
      case near: False
      show ?thesis
      proof (cases "mode < 2 + s_near + s_same")
        case True
        then obtain b r where bs_eq: "bs = b # r"
          using assms mode0 mode1 near
          by (cases bs) (auto simp: decode_address_def)
        then have out:
          "addr = same c ! ((mode - 2 - s_near) * 256 + unat b)"
          "rest = r"
          "c' = cache_update c (same c ! ((mode - 2 - s_near) * 256 + unat b))"
          using assms True mode0 mode1 near
          by (auto simp: decode_address_def Let_def)
        show ?thesis
          using True mode0 mode1 near bs_eq out
          by (simp add: decode_address_def Let_def)
      next
        case False
        then show ?thesis
          using assms mode0 mode1 near by (simp add: decode_address_def)
      qed
    qed
  qed
qed

lemma exec_half_append_tails:
  assumes "exec_half h sz src_seg src_seg_len tgt_len st = Inl st'"
  shows "exec_half h sz src_seg src_seg_len tgt_len
           (dec_state_append st data_tail inst_tail addr_tail)
       = Inl (dec_state_append st' data_tail inst_tail addr_tail)"
  using assms
proof (cases "ity h")
  case NOOP
  then show ?thesis
    using assms by (simp add: exec_half_def dec_state_append_def)
next
  case IADD
  then have sz_data: "sz \<le> length (ds_data_rem st)"
        and tgt_ok: "length (ds_tgt st) + sz \<le> tgt_len"
    using assms by (auto simp: exec_half_def split: if_splits)
  have st'_eq:
    "st' =
     st \<lparr> ds_data_rem := drop sz (ds_data_rem st),
          ds_tgt := ds_tgt st @ take sz (ds_data_rem st) \<rparr>"
    using assms IADD sz_data tgt_ok
    by (simp add: exec_half_def)
  show ?thesis
    using IADD sz_data tgt_ok st'_eq
    by (simp add: exec_half_def dec_state_append_def take_append drop_append)
next
  case IRUN
  then obtain b rest where
    pop: "pop_byte (ds_data_rem st) = Some (b, rest)"
    using assms by (auto simp: exec_half_def split: option.splits if_splits)
  have pop_tail:
    "pop_byte (ds_data_rem st @ data_tail) = Some (b, rest @ data_tail)"
    by (rule pop_byte_append_success[OF pop])
  have tgt_ok: "length (ds_tgt st) + sz \<le> tgt_len"
    using assms IRUN pop by (auto simp: exec_half_def split: if_splits)
  have st'_eq:
    "st' =
     st \<lparr> ds_data_rem := rest,
          ds_tgt := ds_tgt st @ replicate sz b \<rparr>"
    using assms IRUN pop tgt_ok
    by (simp add: exec_half_def)
  show ?thesis
    using IRUN pop pop_tail tgt_ok st'_eq
    by (simp add: exec_half_def dec_state_append_def)
next
  case (ICOPY mode)
  let ?here = "src_seg_len + length (ds_tgt st)"
  obtain addr rest c' where
    dec: "decode_address (ds_cache st) mode ?here (ds_addr_rem st) =
            Some (addr, rest, c')"
    using assms ICOPY
    by (auto simp: exec_half_def Let_def split: option.splits if_splits)
  have dec_tail:
    "decode_address (ds_cache st) mode ?here (ds_addr_rem st @ addr_tail) =
       Some (addr, rest @ addr_tail, c')"
    by (rule decode_address_append_success[OF dec])
  have src_ok:
    "\<not> (addr + sz > src_seg_len + length (ds_tgt st) + sz \<or>
          addr \<ge> src_seg_len + length (ds_tgt st))"
    using assms ICOPY dec by (auto simp: exec_half_def Let_def split: if_splits)
  have tgt_ok: "length (ds_tgt st) + sz \<le> tgt_len"
    using assms ICOPY dec src_ok
    by (auto simp: exec_half_def Let_def split: if_splits)
  have st'_eq:
    "st' =
     st \<lparr> ds_addr_rem := rest,
          ds_cache := c',
          ds_tgt := copy_loop src_seg (ds_tgt st) addr sz \<rparr>"
    using assms ICOPY dec src_ok tgt_ok
    by (simp add: exec_half_def Let_def)
  show ?thesis
    using ICOPY dec dec_tail src_ok tgt_ok st'_eq
    by (simp add: exec_half_def dec_state_append_def Let_def)
qed

lemma decode_one_append_tails:
  assumes "decode_one src_seg src_seg_len tgt_len st = Inl st'"
  shows "decode_one src_seg src_seg_len tgt_len
           (dec_state_append st data_tail inst_tail addr_tail)
       = Inl (dec_state_append st' data_tail inst_tail addr_tail)"
proof -
  obtain op irest where
    pop: "pop_byte (ds_inst_rem st) = Some (op, irest)"
    using assms by (auto simp: decode_one_def split: option.splits)
  define h1 where "h1 = fst (default_entry (unat op))"
  define h2 where "h2 = snd (default_entry (unat op))"
  have entry_eq: "default_entry (unat op) = (h1, h2)"
    by (simp add: h1_def h2_def prod_eq_iff)
  define st1 where "st1 = st \<lparr> ds_inst_rem := irest \<rparr>"
  obtain sz1 irest1 where
    r1: "resolve_size h1 (ds_inst_rem st1) = Some (sz1, irest1)"
    using assms pop h1_def h2_def st1_def
    by (auto simp: decode_one_def Let_def split: option.splits prod.splits sum.splits)
  define st2 where "st2 = st1 \<lparr> ds_inst_rem := irest1 \<rparr>"
  obtain st3 where
    e1: "exec_half h1 sz1 src_seg src_seg_len tgt_len st2 = Inl st3"
    using assms pop h1_def h2_def st1_def st2_def r1
    by (auto simp: decode_one_def Let_def split: option.splits prod.splits sum.splits)
  obtain sz2 irest2 where
    r2: "resolve_size h2 (ds_inst_rem st3) = Some (sz2, irest2)"
    using assms pop h1_def h2_def st1_def st2_def r1 e1
    by (auto simp: decode_one_def Let_def split: option.splits prod.splits sum.splits)
  define st4 where "st4 = st3 \<lparr> ds_inst_rem := irest2 \<rparr>"
  have e2: "exec_half h2 sz2 src_seg src_seg_len tgt_len st4 = Inl st'"
    using assms pop h1_def h2_def st1_def st2_def st4_def r1 e1 r2
    by (auto simp: decode_one_def Let_def split: option.splits prod.splits sum.splits)

  have pop_tail:
    "pop_byte (ds_inst_rem (dec_state_append st data_tail inst_tail addr_tail)) =
       Some (op, irest @ inst_tail)"
    using pop by (simp add: dec_state_append_def pop_byte_append_success)
  have st1_tail:
    "dec_state_append st data_tail inst_tail addr_tail
       \<lparr>ds_inst_rem := irest @ inst_tail\<rparr> =
     dec_state_append st1 data_tail inst_tail addr_tail"
    by (simp add: st1_def dec_state_append_def)
  have r1_tail:
    "resolve_size h1
       (ds_inst_rem (dec_state_append st1 data_tail inst_tail addr_tail)) =
     Some (sz1, irest1 @ inst_tail)"
    using r1 by (simp add: dec_state_append_def resolve_size_append_success)
  have r1_direct:
    "resolve_size h1 (irest @ inst_tail) = Some (sz1, irest1 @ inst_tail)"
    using r1 by (simp add: st1_def resolve_size_append_success)
  have st2_tail:
    "dec_state_append st1 data_tail inst_tail addr_tail
       \<lparr>ds_inst_rem := irest1 @ inst_tail\<rparr> =
     dec_state_append st2 data_tail inst_tail addr_tail"
    by (simp add: st2_def dec_state_append_def)
  have st2_tail_direct:
    "dec_state_append st data_tail inst_tail addr_tail
       \<lparr>ds_inst_rem := irest @ inst_tail,
          ds_inst_rem := irest1 @ inst_tail\<rparr> =
     dec_state_append st2 data_tail inst_tail addr_tail"
    by (simp add: st1_def st2_def dec_state_append_def)
  have e1_tail:
    "exec_half h1 sz1 src_seg src_seg_len tgt_len
       (dec_state_append st2 data_tail inst_tail addr_tail) =
     Inl (dec_state_append st3 data_tail inst_tail addr_tail)"
    by (rule exec_half_append_tails[OF e1])
  have r2_tail:
    "resolve_size h2
       (ds_inst_rem (dec_state_append st3 data_tail inst_tail addr_tail)) =
     Some (sz2, irest2 @ inst_tail)"
    using r2 by (simp add: dec_state_append_def resolve_size_append_success)
  have st4_tail:
    "dec_state_append st3 data_tail inst_tail addr_tail
       \<lparr>ds_inst_rem := irest2 @ inst_tail\<rparr> =
     dec_state_append st4 data_tail inst_tail addr_tail"
    by (simp add: st4_def dec_state_append_def)
  have e2_tail:
    "exec_half h2 sz2 src_seg src_seg_len tgt_len
       (dec_state_append st4 data_tail inst_tail addr_tail) =
     Inl (dec_state_append st' data_tail inst_tail addr_tail)"
    by (rule exec_half_append_tails[OF e2])
  have h1_op:
    "fst (default_entry (unat (fst (op, irest @ inst_tail)))) = h1"
    using entry_eq by simp
  have h2_op:
    "snd (default_entry (unat (fst (op, irest @ inst_tail)))) = h2"
    using entry_eq by simp
  show ?thesis
    unfolding decode_one_def
    using pop_tail st1_tail r1_tail r1_direct st2_tail st2_tail_direct
          e1_tail r2_tail st4_tail e2_tail entry_eq h1_op h2_op
    by (simp add: Let_def split_beta)
qed

lemma decode_loop_append_tails:
  assumes first: "decode_loop n src_seg src_seg_len tgt_len st = Inl st'"
      and second:
        "decode_loop m src_seg src_seg_len tgt_len
           (dec_state_append st' data_tail inst_tail addr_tail) = Inl st''"
  shows "decode_loop (n + m) src_seg src_seg_len tgt_len
           (dec_state_append st data_tail inst_tail addr_tail) = Inl st''"
  using first second
  apply (induct n arbitrary: st)
   apply (subgoal_tac "st' = st")
    apply simp
   apply (cases "ds_inst_rem st = []"; simp split: if_splits)
  subgoal premises prems for n st
  proof (cases "ds_inst_rem st = []")
    case True
    then have st'_eq: "st' = st"
      using prems(2) by simp
    have second_st:
      "decode_loop m src_seg src_seg_len tgt_len
         (dec_state_append st data_tail inst_tail addr_tail) = Inl st''"
      using prems(3) st'_eq by simp
    show ?thesis
      using decode_loop_mono[OF second_st, of "Suc n + m"] by simp
  next
    case False
    obtain st_mid where
      step: "decode_one src_seg src_seg_len tgt_len st = Inl st_mid"
      and rest: "decode_loop n src_seg src_seg_len tgt_len st_mid = Inl st'"
      using prems(2) False by (auto split: sum.splits)
    have step_tail:
      "decode_one src_seg src_seg_len tgt_len
         (dec_state_append st data_tail inst_tail addr_tail) =
       Inl (dec_state_append st_mid data_tail inst_tail addr_tail)"
      by (rule decode_one_append_tails[OF step])
    have rest_tail:
      "decode_loop (n + m) src_seg src_seg_len tgt_len
         (dec_state_append st_mid data_tail inst_tail addr_tail) = Inl st''"
      using prems(1)[OF rest prems(3)] .
    show ?thesis
      using False step_tail rest_tail
      by (simp add: dec_state_append_def)
  qed
  done

lemma section_decodes_prefix_empty:
  "section_decodes_prefix src_seg tgt_len [] [] [] c tgt tgt c"
  by (simp add: section_decodes_prefix_def)

lemma section_decodes_prefix_append:
  assumes first:
    "section_decodes_prefix src_seg tgt_len data1 inst1 addr1 c0 tgt0 tgt1 c1"
  assumes second:
    "section_decodes_prefix src_seg tgt_len data2 inst2 addr2 c1 tgt1 tgt2 c2"
  shows
    "section_decodes_prefix src_seg tgt_len
       (data1 @ data2) (inst1 @ inst2) (addr1 @ addr2) c0 tgt0 tgt2 c2"
proof -
  let ?st0 =
    "\<lparr> ds_data_rem = data1, ds_inst_rem = inst1, ds_addr_rem = addr1,
       ds_cache = c0, ds_tgt = tgt0 \<rparr>"
  let ?st1 =
    "\<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = [],
       ds_cache = c1, ds_tgt = tgt1 \<rparr>"
  let ?st2 =
    "\<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = [],
       ds_cache = c2, ds_tgt = tgt2 \<rparr>"
  have first_loop:
    "decode_loop (length inst1) src_seg (length src_seg) tgt_len ?st0 = Inl ?st1"
    using first by (simp add: section_decodes_prefix_def)
  have second_loop:
    "decode_loop (length inst2) src_seg (length src_seg) tgt_len
       (dec_state_append ?st1 data2 inst2 addr2) = Inl ?st2"
    using second by (simp add: section_decodes_prefix_def dec_state_append_def)
  have combined:
    "decode_loop (length inst1 + length inst2) src_seg (length src_seg) tgt_len
       (dec_state_append ?st0 data2 inst2 addr2) = Inl ?st2"
    by (rule decode_loop_append_tails[OF first_loop second_loop])
  show ?thesis
    using combined
    by (simp add: section_decodes_prefix_def dec_state_append_def)
qed

lemma add_inst_bytes_nonempty[simp]:
  "add_inst_bytes n \<noteq> []"
  by (auto simp: add_inst_bytes_def Let_def split: prod.splits)

lemma run_inst_bytes_nonempty[simp]:
  "run_inst_bytes n \<noteq> []"
  by (auto simp: run_inst_bytes_def Let_def split: prod.splits)

lemma copy_inst_bytes_nonempty[simp]:
  "copy_inst_bytes n mode \<noteq> []"
  by (auto simp: copy_inst_bytes_def Let_def split: prod.splits)

lemma section_decodes_prefix_add:
  assumes "length bs < 2 ^ 32"
      and "length tgt + length bs \<le> tgt_len"
  shows
    "section_decodes_prefix src_seg tgt_len
       bs (add_inst_bytes (length bs)) [] c tgt (tgt @ bs) c"
proof -
  let ?st =
    "\<lparr> ds_data_rem = undefined, ds_inst_rem = undefined,
       ds_addr_rem = undefined, ds_cache = c, ds_tgt = tgt \<rparr>"
  have raw:
    "let (op_code, needs_sz) = find_single_add_opcode (length bs);
         inst_bytes = [word_of_nat op_code :: byte] @
                      (if needs_sz then varint_encode (length bs) else [])
     in decode_one src_seg (length src_seg) tgt_len
          (?st \<lparr> ds_data_rem := bs @ [], ds_inst_rem := inst_bytes @ [],
                ds_addr_rem := [] \<rparr>)
        = Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [],
                  ds_addr_rem := [], ds_tgt := ds_tgt ?st @ bs \<rparr>)"
    by (rule decode_one_add_suffix
        [where st = ?st and data_rest = "[]" and inst_rest = "[]"
           and addr_rest = "[]" and src_seg = src_seg
           and src_seg_len = "length src_seg" and tgt_len = tgt_len and bs = bs])
       (use assms in simp_all)
  then have step:
    "decode_one src_seg (length src_seg) tgt_len
       (?st \<lparr> ds_data_rem := bs, ds_inst_rem := add_inst_bytes (length bs),
              ds_addr_rem := [] \<rparr>) =
     Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [], ds_addr_rem := [],
              ds_tgt := tgt @ bs \<rparr>)"
    by (simp add: add_inst_bytes_def Let_def split_def)
  obtain op rest where inst_eq: "add_inst_bytes (length bs) = op # rest"
    by (cases "add_inst_bytes (length bs)") simp_all
  let ?st_done =
    "\<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = [],
       ds_cache = c, ds_tgt = tgt @ bs \<rparr>"
  have loop_done:
    "decode_loop (length rest) src_seg (length src_seg) tgt_len ?st_done = Inl ?st_done"
    by (rule decode_loop_fuel_empty) simp
  show ?thesis
    using step inst_eq loop_done
    by (simp add: section_decodes_prefix_def)
qed

lemma section_decodes_prefix_run:
  assumes "n > 0" "n < 2 ^ 32"
      and "length tgt + n \<le> tgt_len"
  shows
    "section_decodes_prefix src_seg tgt_len
       [b] (run_inst_bytes n) [] c tgt (tgt @ replicate n b) c"
proof -
  let ?st =
    "\<lparr> ds_data_rem = undefined, ds_inst_rem = undefined,
       ds_addr_rem = undefined, ds_cache = c, ds_tgt = tgt \<rparr>"
  have raw:
    "decode_one src_seg (length src_seg) tgt_len
       (?st \<lparr> ds_data_rem := b # [], ds_inst_rem := (0 :: byte) # varint_encode n @ [],
              ds_addr_rem := [] \<rparr>) =
     Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [], ds_addr_rem := [],
              ds_tgt := ds_tgt ?st @ replicate n b \<rparr>)"
    by (rule decode_one_run_suffix
        [where st = ?st and data_rest = "[]" and inst_rest = "[]"
           and addr_rest = "[]" and src_seg = src_seg
           and src_seg_len = "length src_seg" and tgt_len = tgt_len and n = n])
       (use assms in simp_all)
  then have step:
    "decode_one src_seg (length src_seg) tgt_len
       (?st \<lparr> ds_data_rem := [b], ds_inst_rem := run_inst_bytes n,
              ds_addr_rem := [] \<rparr>) =
     Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [], ds_addr_rem := [],
              ds_tgt := tgt @ replicate n b \<rparr>)"
    by (simp add: run_inst_bytes_def find_single_run_opcode_def)
  obtain op rest where inst_eq: "run_inst_bytes n = op # rest"
    by (cases "run_inst_bytes n") simp_all
  let ?st_done =
    "\<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = [],
       ds_cache = c, ds_tgt = tgt @ replicate n b \<rparr>"
  have loop_done:
    "decode_loop (length rest) src_seg (length src_seg) tgt_len ?st_done = Inl ?st_done"
    by (rule decode_loop_fuel_empty) simp
  show ?thesis
    using step inst_eq loop_done
    by (simp add: section_decodes_prefix_def)
qed

lemma section_decodes_prefix_copy:
  assumes "mode \<le> 8" "n > 0" "n < 2 ^ 32"
      and "a < 2 ^ 32"
      and "length src_seg + length tgt < 2 ^ 32"
      and "a < length src_seg + length tgt"
      and "length tgt + n \<le> tgt_len"
      and "wf_encoding c a (length src_seg + length tgt) mode abytes"
  shows
    "section_decodes_prefix src_seg tgt_len
       [] (copy_inst_bytes n mode) abytes c tgt
       (copy_loop src_seg tgt a n) (cache_update c a)"
proof -
  let ?st =
    "\<lparr> ds_data_rem = undefined, ds_inst_rem = undefined,
       ds_addr_rem = undefined, ds_cache = c, ds_tgt = tgt \<rparr>"
  have raw:
    "let (op_code, needs_sz) = find_single_copy_opcode n mode;
         inst_bytes = [word_of_nat op_code :: byte] @
                      (if needs_sz then varint_encode n else [])
     in decode_one src_seg (length src_seg) tgt_len
          (?st \<lparr> ds_data_rem := [], ds_inst_rem := inst_bytes @ [],
                ds_addr_rem := abytes @ [] \<rparr>)
        = Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [],
                  ds_addr_rem := [],
                  ds_cache := cache_update (ds_cache ?st) a,
                  ds_tgt := copy_loop src_seg (ds_tgt ?st) a n \<rparr>)"
    by (rule decode_one_copy_suffix
        [where st = ?st and data_rest = "[]" and inst_rest = "[]"
           and addr_rest = "[]" and src_seg = src_seg
           and src_seg_len = "length src_seg" and tgt_len = tgt_len
           and n = n and mode = mode and a = a and abytes = abytes])
       (use assms in simp_all)
  then have step:
    "decode_one src_seg (length src_seg) tgt_len
       (?st \<lparr> ds_data_rem := [], ds_inst_rem := copy_inst_bytes n mode,
              ds_addr_rem := abytes \<rparr>) =
     Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [], ds_addr_rem := [],
              ds_cache := cache_update c a,
              ds_tgt := copy_loop src_seg tgt a n \<rparr>)"
    by (simp add: copy_inst_bytes_def Let_def split_def)
  obtain op rest where inst_eq: "copy_inst_bytes n mode = op # rest"
    by (cases "copy_inst_bytes n mode") simp_all
  let ?st_done =
    "\<lparr> ds_data_rem = [], ds_inst_rem = [], ds_addr_rem = [],
       ds_cache = cache_update c a, ds_tgt = copy_loop src_seg tgt a n \<rparr>"
  have loop_done:
    "decode_loop (length rest) src_seg (length src_seg) tgt_len ?st_done = Inl ?st_done"
    by (rule decode_loop_fuel_empty) simp
  show ?thesis
    using step inst_eq loop_done
    by (simp add: section_decodes_prefix_def)
qed

lemma find_add_copy_opcode_less_256:
  assumes "find_add_copy_opcode add_sz copy_sz mode = Some op"
  shows "op < 256"
  using assms
  by (auto simp: find_add_copy_opcode_def split: if_splits)

lemma find_add_copy_opcode_default_entry:
  assumes fop: "find_add_copy_opcode add_sz copy_sz mode = Some op"
  shows "default_entry op = (add_hi add_sz, copy_hi copy_sz mode)"
proof -
  have add_ge: "1 \<le> add_sz" and add_le: "add_sz \<le> 4"
    using fop by (auto simp: find_add_copy_opcode_def split: if_splits)
  have repr:
    "(mode \<le> 5 \<and> 4 \<le> copy_sz \<and> copy_sz \<le> 6) \<or>
     (6 \<le> mode \<and> mode \<le> 8 \<and> copy_sz = 4)"
    using fop by (auto simp: find_add_copy_opcode_def split: if_splits)
  obtain op' where
    fop': "find_add_copy_opcode add_sz copy_sz mode = Some op'"
    and entry: "default_entry op' = (add_hi add_sz, copy_hi copy_sz mode)"
    using default_entry_add_copy[OF add_ge add_le repr] by auto
  have "op' = op"
    using fop fop' by simp
  then show ?thesis using entry by simp
qed

lemma find_copy_add_opcode_less_256:
  assumes "find_copy_add_opcode copy_sz mode add_sz = Some op"
  shows "op < 256"
  using assms
  by (auto simp: find_copy_add_opcode_def split: if_splits)

lemma find_copy_add_opcode_default_entry:
  assumes fop: "find_copy_add_opcode copy_sz mode add_sz = Some op"
  shows "default_entry op = (copy_hi copy_sz mode, add_hi add_sz)"
proof -
  have copy_eq: "copy_sz = 4" and add_eq: "add_sz = 1" and mode_le: "mode \<le> 8"
    using fop by (auto simp: find_copy_add_opcode_def split: if_splits)
  have op_eq: "op = 247 + mode"
    using fop copy_eq add_eq mode_le by (simp add: find_copy_add_opcode_def)
  show ?thesis
    using default_entry_copy_add[OF mode_le]
    by (simp add: op_eq copy_eq add_eq)
qed

lemma decode_one_add_copy_fused_suffix:
  assumes fop: "find_add_copy_opcode (length add_bs) copy_n mode = Some op"
      and addr32: "a < 2 ^ 32"
      and here32:
        "src_seg_len + length (ds_tgt st) + length add_bs < 2 ^ 32"
      and addr_ok:
        "a < src_seg_len + length (ds_tgt st) + length add_bs"
      and tgt_ok:
        "length (ds_tgt st) + length add_bs + copy_n \<le> tgt_len"
      and wf:
        "wf_encoding (ds_cache st) a
           (src_seg_len + length (ds_tgt st) + length add_bs) mode abytes"
  shows
    "decode_one src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := add_bs @ data_rest
           , ds_inst_rem := [word_of_nat op]
           , ds_addr_rem := abytes @ addr_rest \<rparr>) =
     Inl (st \<lparr> ds_data_rem := data_rest
             , ds_inst_rem := []
             , ds_addr_rem := addr_rest
             , ds_cache := cache_update (ds_cache st) a
             , ds_tgt := copy_loop src_seg (ds_tgt st @ add_bs) a copy_n \<rparr>)"
proof -
  have op_unat: "unat (word_of_nat op :: byte) = op"
    using find_add_copy_opcode_less_256[OF fop]
    by (simp add: unat_of_nat_eq)
  have entry: "default_entry op =
        (add_hi (length add_bs), copy_hi copy_n mode)"
    by (rule find_add_copy_opcode_default_entry[OF fop])
  have add_pos: "length add_bs > 0"
    using fop by (auto simp: find_add_copy_opcode_def split: if_splits)
  have copy_pos: "copy_n > 0"
    using fop by (auto simp: find_add_copy_opcode_def split: if_splits)
  let ?here = "src_seg_len + length (ds_tgt st) + length add_bs"
  have dec: "decode_address (ds_cache st) mode ?here (abytes @ addr_rest) =
      Some (a, addr_rest, cache_update (ds_cache st) a)"
    using wf_encoding_decodes[OF wf addr32 here32] .
  have dec_after_add:
    "decode_address (ds_cache st) mode
       (src_seg_len + length (ds_tgt st @ add_bs)) (abytes @ addr_rest) =
     Some (a, addr_rest, cache_update (ds_cache st) a)"
    using dec by (simp add: add.assoc)
  have add_tgt_ok: "length (ds_tgt st) + length add_bs \<le> tgt_len"
    using tgt_ok by simp
  have copy_tgt_ok: "length (ds_tgt st @ add_bs) + copy_n \<le> tgt_len"
    using tgt_ok by simp
  have copy_tgt_not_bad:
    "\<not> tgt_len < length (ds_tgt st @ add_bs) + copy_n"
    using copy_tgt_ok by simp
  have src_ok:
    "\<not> (a + copy_n > src_seg_len + length (ds_tgt st @ add_bs) + copy_n
        \<or> a \<ge> src_seg_len + length (ds_tgt st @ add_bs))"
    using addr_ok by simp
  have src_not_bad:
    "\<not> (src_seg_len + length (ds_tgt st @ add_bs) + copy_n < a + copy_n
        \<or> src_seg_len + length (ds_tgt st @ add_bs) \<le> a)"
    using addr_ok by simp
  show ?thesis
    unfolding decode_one_def pop_byte_def Let_def
    using op_unat entry add_pos copy_pos dec dec_after_add add_tgt_ok
          copy_tgt_ok copy_tgt_not_bad src_ok src_not_bad
    by (simp add: resolve_size_def exec_half_def add_hi_def copy_hi_def)
qed

lemma section_decodes_prefix_add_copy_fused:
  assumes fop: "find_add_copy_opcode (length add_bs) copy_n mode = Some op"
      and "a < 2 ^ 32"
      and "length src_seg + length tgt + length add_bs < 2 ^ 32"
      and "a < length src_seg + length tgt + length add_bs"
      and "length tgt + length add_bs + copy_n \<le> tgt_len"
      and "wf_encoding c a (length src_seg + length tgt + length add_bs) mode abytes"
  shows
    "section_decodes_prefix src_seg tgt_len
       add_bs [word_of_nat op] abytes c tgt
       (copy_loop src_seg (tgt @ add_bs) a copy_n) (cache_update c a)"
proof -
  let ?st =
    "\<lparr> ds_data_rem = undefined, ds_inst_rem = undefined,
       ds_addr_rem = undefined, ds_cache = c, ds_tgt = tgt \<rparr>"
  have raw:
    "decode_one src_seg (length src_seg) tgt_len
       (?st \<lparr> ds_data_rem := add_bs @ [], ds_inst_rem := [word_of_nat op],
              ds_addr_rem := abytes @ [] \<rparr>) =
     Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [], ds_addr_rem := [],
              ds_cache := cache_update (ds_cache ?st) a,
              ds_tgt := copy_loop src_seg (ds_tgt ?st @ add_bs) a copy_n \<rparr>)"
    by (rule decode_one_add_copy_fused_suffix
        [where st = ?st and data_rest = "[]" and addr_rest = "[]"
           and src_seg = src_seg and src_seg_len = "length src_seg"
           and tgt_len = tgt_len and add_bs = add_bs and copy_n = copy_n
           and mode = mode and op = op and a = a and abytes = abytes])
       (use assms in simp_all)
  then have step:
    "decode_one src_seg (length src_seg) tgt_len
       (?st \<lparr> ds_data_rem := add_bs, ds_inst_rem := [word_of_nat op],
              ds_addr_rem := abytes \<rparr>) =
     Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [], ds_addr_rem := [],
              ds_cache := cache_update c a,
              ds_tgt := copy_loop src_seg (tgt @ add_bs) a copy_n \<rparr>)"
    by simp
  show ?thesis
    using step by (simp add: section_decodes_prefix_def)
qed

lemma decode_one_copy_add_fused_suffix:
  assumes fop: "find_copy_add_opcode copy_n mode (length add_bs) = Some op"
      and addr32: "a < 2 ^ 32"
      and here32: "src_seg_len + length (ds_tgt st) < 2 ^ 32"
      and addr_ok: "a < src_seg_len + length (ds_tgt st)"
      and tgt_ok: "length (ds_tgt st) + copy_n + length add_bs \<le> tgt_len"
      and wf:
        "wf_encoding (ds_cache st) a
           (src_seg_len + length (ds_tgt st)) mode abytes"
  shows
    "decode_one src_seg src_seg_len tgt_len
       (st \<lparr> ds_data_rem := add_bs @ data_rest
           , ds_inst_rem := [word_of_nat op]
           , ds_addr_rem := abytes @ addr_rest \<rparr>) =
     Inl (st \<lparr> ds_data_rem := data_rest
             , ds_inst_rem := []
             , ds_addr_rem := addr_rest
             , ds_cache := cache_update (ds_cache st) a
             , ds_tgt := copy_loop src_seg (ds_tgt st) a copy_n @ add_bs \<rparr>)"
proof -
  have op_unat: "unat (word_of_nat op :: byte) = op"
    using find_copy_add_opcode_less_256[OF fop]
    by (simp add: unat_of_nat_eq)
  have entry: "default_entry op =
        (copy_hi copy_n mode, add_hi (length add_bs))"
    by (rule find_copy_add_opcode_default_entry[OF fop])
  have add_pos: "length add_bs > 0"
    using fop by (auto simp: find_copy_add_opcode_def split: if_splits)
  have copy_pos: "copy_n > 0"
    using fop by (auto simp: find_copy_add_opcode_def split: if_splits)
  let ?here = "src_seg_len + length (ds_tgt st)"
  have dec: "decode_address (ds_cache st) mode ?here (abytes @ addr_rest) =
      Some (a, addr_rest, cache_update (ds_cache st) a)"
    using wf_encoding_decodes[OF wf addr32 here32] .
  have copy_tgt_ok: "length (ds_tgt st) + copy_n \<le> tgt_len"
    using tgt_ok by simp
  have copy_tgt_not_bad:
    "\<not> tgt_len < length (ds_tgt st) + copy_n"
    using copy_tgt_ok by simp
  have add_tgt_ok:
    "length (copy_loop src_seg (ds_tgt st) a copy_n) + length add_bs \<le> tgt_len"
    using tgt_ok by (simp add: copy_loop_length)
  have add_tgt_not_bad:
    "\<not> tgt_len < length (copy_loop src_seg (ds_tgt st) a copy_n) + length add_bs"
    using add_tgt_ok by simp
  have src_ok:
    "\<not> (a + copy_n > src_seg_len + length (ds_tgt st) + copy_n
        \<or> a \<ge> src_seg_len + length (ds_tgt st))"
    using addr_ok by simp
  have src_not_bad:
    "\<not> (src_seg_len + length (ds_tgt st) + copy_n < a + copy_n
        \<or> src_seg_len + length (ds_tgt st) \<le> a)"
    using addr_ok by simp
  show ?thesis
    unfolding decode_one_def pop_byte_def Let_def
    using op_unat entry add_pos copy_pos dec copy_tgt_ok copy_tgt_not_bad
          add_tgt_ok add_tgt_not_bad src_ok src_not_bad
    by (simp add: resolve_size_def exec_half_def add_hi_def copy_hi_def)
qed

lemma section_decodes_prefix_copy_add_fused:
  assumes fop: "find_copy_add_opcode copy_n mode (length add_bs) = Some op"
      and "a < 2 ^ 32"
      and "length src_seg + length tgt < 2 ^ 32"
      and "a < length src_seg + length tgt"
      and "length tgt + copy_n + length add_bs \<le> tgt_len"
      and "wf_encoding c a (length src_seg + length tgt) mode abytes"
  shows
    "section_decodes_prefix src_seg tgt_len
       add_bs [word_of_nat op] abytes c tgt
       (copy_loop src_seg tgt a copy_n @ add_bs) (cache_update c a)"
proof -
  let ?st =
    "\<lparr> ds_data_rem = undefined, ds_inst_rem = undefined,
       ds_addr_rem = undefined, ds_cache = c, ds_tgt = tgt \<rparr>"
  have raw:
    "decode_one src_seg (length src_seg) tgt_len
       (?st \<lparr> ds_data_rem := add_bs @ [], ds_inst_rem := [word_of_nat op],
              ds_addr_rem := abytes @ [] \<rparr>) =
     Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [], ds_addr_rem := [],
              ds_cache := cache_update (ds_cache ?st) a,
              ds_tgt := copy_loop src_seg (ds_tgt ?st) a copy_n @ add_bs \<rparr>)"
    by (rule decode_one_copy_add_fused_suffix
        [where st = ?st and data_rest = "[]" and addr_rest = "[]"
           and src_seg = src_seg and src_seg_len = "length src_seg"
           and tgt_len = tgt_len and add_bs = add_bs and copy_n = copy_n
           and mode = mode and op = op and a = a and abytes = abytes])
       (use assms in simp_all)
  then have step:
    "decode_one src_seg (length src_seg) tgt_len
       (?st \<lparr> ds_data_rem := add_bs, ds_inst_rem := [word_of_nat op],
              ds_addr_rem := abytes \<rparr>) =
     Inl (?st \<lparr> ds_data_rem := [], ds_inst_rem := [], ds_addr_rem := [],
              ds_cache := cache_update c a,
              ds_tgt := copy_loop src_seg tgt a copy_n @ add_bs \<rparr>)"
    by simp
  show ?thesis
    using step by (simp add: section_decodes_prefix_def)
qed

lemma section_decodes_prefix_append_add:
  assumes old:
    "section_decodes_prefix src_seg tgt_len data inst addr c0 tgt0 tgt c"
      and len32: "length bs < 2 ^ 32"
      and tgt_ok: "length tgt + length bs \<le> tgt_len"
  shows
    "section_decodes_prefix src_seg tgt_len
       (data @ bs) (inst @ add_inst_bytes (length bs)) addr
       c0 tgt0 (tgt @ bs) c"
  using section_decodes_prefix_append
        [OF old section_decodes_prefix_add[OF len32 tgt_ok]]
  by simp

lemma section_decodes_prefix_append_run:
  assumes old:
    "section_decodes_prefix src_seg tgt_len data inst addr c0 tgt0 tgt c"
      and n_pos: "n > 0" and n32: "n < 2 ^ 32"
      and tgt_ok: "length tgt + n \<le> tgt_len"
  shows
    "section_decodes_prefix src_seg tgt_len
       (data @ [b]) (inst @ run_inst_bytes n) addr
       c0 tgt0 (tgt @ replicate n b) c"
  using section_decodes_prefix_append
        [OF old section_decodes_prefix_run[OF n_pos n32 tgt_ok]]
  by simp

lemma section_decodes_prefix_append_copy:
  assumes old:
    "section_decodes_prefix src_seg tgt_len data inst addr c0 tgt0 tgt c"
      and mode: "mode \<le> 8" and n_pos: "n > 0" and n32: "n < 2 ^ 32"
      and a32: "a < 2 ^ 32"
      and here32: "length src_seg + length tgt < 2 ^ 32"
      and addr_ok: "a < length src_seg + length tgt"
      and tgt_ok: "length tgt + n \<le> tgt_len"
      and wf: "wf_encoding c a (length src_seg + length tgt) mode abytes"
  shows
    "section_decodes_prefix src_seg tgt_len
       data (inst @ copy_inst_bytes n mode) (addr @ abytes)
       c0 tgt0 (copy_loop src_seg tgt a n) (cache_update c a)"
  using section_decodes_prefix_append
        [OF old section_decodes_prefix_copy
          [OF mode n_pos n32 a32 here32 addr_ok tgt_ok wf]]
  by simp

lemma section_decodes_prefix_append_add_copy_fused:
  assumes old:
    "section_decodes_prefix src_seg tgt_len data inst addr c0 tgt0 tgt c"
      and fop: "find_add_copy_opcode (length add_bs) copy_n mode = Some op"
      and a32: "a < 2 ^ 32"
      and here32: "length src_seg + length tgt + length add_bs < 2 ^ 32"
      and addr_ok: "a < length src_seg + length tgt + length add_bs"
      and tgt_ok: "length tgt + length add_bs + copy_n \<le> tgt_len"
      and wf: "wf_encoding c a (length src_seg + length tgt + length add_bs) mode abytes"
  shows
    "section_decodes_prefix src_seg tgt_len
       (data @ add_bs) (inst @ [word_of_nat op]) (addr @ abytes)
       c0 tgt0 (copy_loop src_seg (tgt @ add_bs) a copy_n)
       (cache_update c a)"
  using section_decodes_prefix_append
        [OF old section_decodes_prefix_add_copy_fused
          [OF fop a32 here32 addr_ok tgt_ok wf]]
  by simp

lemma section_decodes_prefix_append_copy_add_fused:
  assumes old:
    "section_decodes_prefix src_seg tgt_len data inst addr c0 tgt0 tgt c"
      and fop: "find_copy_add_opcode copy_n mode (length add_bs) = Some op"
      and a32: "a < 2 ^ 32"
      and here32: "length src_seg + length tgt < 2 ^ 32"
      and addr_ok: "a < length src_seg + length tgt"
      and tgt_ok: "length tgt + copy_n + length add_bs \<le> tgt_len"
      and wf: "wf_encoding c a (length src_seg + length tgt) mode abytes"
  shows
    "section_decodes_prefix src_seg tgt_len
       (data @ add_bs) (inst @ [word_of_nat op]) (addr @ abytes)
       c0 tgt0 (copy_loop src_seg tgt a copy_n @ add_bs)
       (cache_update c a)"
  using section_decodes_prefix_append
        [OF old section_decodes_prefix_copy_add_fused
          [OF fop a32 here32 addr_ok tgt_ok wf]]
  by simp

lemma section_decodes_append_add:
  assumes old: "section_decodes src_seg tgt_len data inst addr tgt c"
      and len32: "length bs < 2 ^ 32"
      and tgt_ok: "length tgt + length bs \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       (data @ bs) (inst @ add_inst_bytes (length bs)) addr
       (tgt @ bs) c"
  by (rule section_decodesI,
      rule section_decodes_prefix_append_add[OF section_decodesD[OF old] len32 tgt_ok])

lemma section_decodes_append_run:
  assumes old: "section_decodes src_seg tgt_len data inst addr tgt c"
      and n_pos: "n > 0" and n32: "n < 2 ^ 32"
      and tgt_ok: "length tgt + n \<le> tgt_len"
  shows
    "section_decodes src_seg tgt_len
       (data @ [b]) (inst @ run_inst_bytes n) addr
       (tgt @ replicate n b) c"
  by (rule section_decodesI,
      rule section_decodes_prefix_append_run[OF section_decodesD[OF old] n_pos n32 tgt_ok])

lemma section_decodes_append_copy:
  assumes old: "section_decodes src_seg tgt_len data inst addr tgt c"
      and mode: "mode \<le> 8" and n_pos: "n > 0" and n32: "n < 2 ^ 32"
      and a32: "a < 2 ^ 32"
      and here32: "length src_seg + length tgt < 2 ^ 32"
      and addr_ok: "a < length src_seg + length tgt"
      and tgt_ok: "length tgt + n \<le> tgt_len"
      and wf: "wf_encoding c a (length src_seg + length tgt) mode abytes"
  shows
    "section_decodes src_seg tgt_len
       data (inst @ copy_inst_bytes n mode) (addr @ abytes)
       (copy_loop src_seg tgt a n) (cache_update c a)"
  by (rule section_decodesI,
      rule section_decodes_prefix_append_copy
        [OF section_decodesD[OF old] mode n_pos n32 a32 here32 addr_ok tgt_ok wf])

lemma section_decodes_append_add_copy_fused:
  assumes old: "section_decodes src_seg tgt_len data inst addr tgt c"
      and fop: "find_add_copy_opcode (length add_bs) copy_n mode = Some op"
      and a32: "a < 2 ^ 32"
      and here32: "length src_seg + length tgt + length add_bs < 2 ^ 32"
      and addr_ok: "a < length src_seg + length tgt + length add_bs"
      and tgt_ok: "length tgt + length add_bs + copy_n \<le> tgt_len"
      and wf: "wf_encoding c a (length src_seg + length tgt + length add_bs) mode abytes"
  shows
    "section_decodes src_seg tgt_len
       (data @ add_bs) (inst @ [word_of_nat op]) (addr @ abytes)
       (copy_loop src_seg (tgt @ add_bs) a copy_n) (cache_update c a)"
  by (rule section_decodesI,
      rule section_decodes_prefix_append_add_copy_fused
        [OF section_decodesD[OF old] fop a32 here32 addr_ok tgt_ok wf])

lemma section_decodes_append_copy_add_fused:
  assumes old: "section_decodes src_seg tgt_len data inst addr tgt c"
      and fop: "find_copy_add_opcode copy_n mode (length add_bs) = Some op"
      and a32: "a < 2 ^ 32"
      and here32: "length src_seg + length tgt < 2 ^ 32"
      and addr_ok: "a < length src_seg + length tgt"
      and tgt_ok: "length tgt + copy_n + length add_bs \<le> tgt_len"
      and wf: "wf_encoding c a (length src_seg + length tgt) mode abytes"
  shows
    "section_decodes src_seg tgt_len
       (data @ add_bs) (inst @ [word_of_nat op]) (addr @ abytes)
       (copy_loop src_seg tgt a copy_n @ add_bs) (cache_update c a)"
  by (rule section_decodesI,
      rule section_decodes_prefix_append_copy_add_fused
        [OF section_decodesD[OF old] fop a32 here32 addr_ok tgt_ok wf])

context vcdiff_enc_global_addresses begin


definition enc_sections_inv ::
  "lifted_globals \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> 8 word ptr \<Rightarrow> sections_t_C \<Rightarrow>
   byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow>
   byte list \<Rightarrow> cache \<Rightarrow> bool" where
  "enc_sections_inv s data inst addr sec src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out \<longleftrightarrow>
     emitted_sections s data inst addr sec data_bytes inst_bytes addr_bytes \<and>
     section_decodes src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out"

lemma enc_sections_invD:
  assumes "enc_sections_inv s data inst addr sec src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out"
  shows "emitted_sections s data inst addr sec data_bytes inst_bytes addr_bytes"
        "section_decodes src_seg tgt_len data_bytes inst_bytes addr_bytes target c_out"
  using assms by (simp_all add: enc_sections_inv_def)

end

end
