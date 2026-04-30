(*
  VCDIFF address-cache spec.

  Two caches, both reset to zero at window start:
    near: circular buffer of 4 most-recent COPY addresses.
    same: 3 banks × 256 entries, indexed by (addr mod 256) within a bank.

  Modes:
    0      VCD_SELF    — varint(addr)
    1      VCD_HERE    — varint(here - addr)
    2..5   NEAR[0..3]  — varint(addr - near[i])
    6..8   SAME[0..2]  — one byte (addr mod 256)

  Mirrors encoder/vcdiff_enc.c's best_mode + cache_update, and
  decoder/vcdiff_dec.c's decode_address + the mode dispatch. The pure spec
  is Lean-style: functions take and return a cache state explicitly.
*)
theory AddressCache
  imports Bytes Varint
begin

unbundle bit_operations_syntax

(* ---------- Cache sizes (default) ---------- *)
definition s_near :: nat where "s_near = 4"
definition s_same :: nat where "s_same = 3"
definition same_buckets :: nat where "same_buckets = s_same * 256"

lemma s_near_pos [simp]: "0 < s_near" by (simp add: s_near_def)
lemma s_same_pos [simp]: "0 < s_same" by (simp add: s_same_def)

(* ---------- State ---------- *)
(*
  `near` has length s_near, `same` has length same_buckets. The cache-
  initialisation function is the only constructor used by the roundtrip
  proof; arbitrary cache states aren't reachable from a fresh window.
*)
record cache =
  near     :: "nat list"
  near_ptr :: nat
  same     :: "nat list"

definition cache_init :: cache where
  "cache_init =
     \<lparr> near = replicate s_near 0
     , near_ptr = 0
     , same = replicate same_buckets 0 \<rparr>"

(* ---------- Updates ---------- *)

definition cache_update :: "cache \<Rightarrow> nat \<Rightarrow> cache" where
  "cache_update c addr =
     c \<lparr> near := (near c)[near_ptr c := addr]
       , near_ptr := (near_ptr c + 1) mod s_near
       , same := (same c)[addr mod same_buckets := addr] \<rparr>"

(* ---------- Mode count ---------- *)
definition num_modes :: nat where
  "num_modes = 2 + s_near + s_same"

lemma num_modes_eq_9 [simp]: "num_modes = 9"
  by (simp add: num_modes_def s_near_def s_same_def)

(* ---------- Encode: pick cheapest mode ---------- *)

(* Try a candidate mode/encoding. Returns the new best if strictly smaller. *)
definition try_better ::
    "nat \<times> byte list \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> nat \<times> byte list" where
  "try_better best mode enc =
     (if length enc < length (snd best) then (mode, enc) else best)"

(* Consider NEAR mode i. *)
definition try_near_mode ::
    "cache \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> byte list \<Rightarrow> nat \<times> byte list" where
  "try_near_mode c addr i best =
     (let base = near c ! i in
      if addr \<ge> base
      then try_better best (2 + i) (varint_encode (addr - base))
      else best)"

fun try_near_modes ::
    "cache \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> byte list \<Rightarrow> nat \<times> byte list" where
  "try_near_modes c addr 0 best = best"
| "try_near_modes c addr (Suc k) best =
     try_near_modes c addr k (try_near_mode c addr (s_near - Suc k) best)"

(* SAME modes: check each bank; first hit (addr != 0) wins. Zero-init
   protection comes from the `addr \<noteq> 0` guard, matching the C. *)
definition try_same_mode ::
    "cache \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> byte list \<Rightarrow> nat \<times> byte list" where
  "try_same_mode c addr bank best =
     (let slot = bank * 256 + addr mod 256 in
      if same c ! slot = addr \<and> addr \<noteq> 0
      then try_better best (2 + s_near + bank)
             [word_of_nat (addr mod 256)]
      else best)"

fun try_same_modes ::
    "cache \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> byte list \<Rightarrow> nat \<times> byte list" where
  "try_same_modes c addr 0 best = best"
| "try_same_modes c addr (Suc k) best =
     try_same_modes c addr k (try_same_mode c addr (s_same - Suc k) best)"

(* Choose mode 0..8 and encoded bytes producing the cheapest representation
   of `addr` relative to the current cache and `here`. Returns the updated
   cache as well. *)
definition encode_address ::
    "cache \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> byte list \<times> cache" where
  "encode_address c addr here =
     (let enc0  = varint_encode addr;
          best0 = (0, enc0);
          best1 =
            (if here > addr
             then try_better best0 1 (varint_encode (here - addr))
             else best0);
          best2 = try_near_modes c addr s_near best1;
          best3 = try_same_modes c addr s_same best2
      in (fst best3, snd best3, cache_update c addr))"

(* ---------- Decode ---------- *)

(*
  Decoder-side address decoding. Returns None on any malformed input
  (truncated varint, bad mode). Matches decoder/vcdiff_dec.c's
  decode_address.

  The decoder operates on a prefix of the address section; the returned
  byte list is the untouched tail.
*)
definition decode_address ::
    "cache \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> (nat \<times> byte list \<times> cache) option" where
  "decode_address c mode here bs =
     (if mode = 0 then
        case varint_decode bs of
          None \<Rightarrow> None
        | Some (addr, rest) \<Rightarrow> Some (addr, rest, cache_update c addr)
      else if mode = 1 then
        case varint_decode bs of
          None \<Rightarrow> None
        | Some (v, rest) \<Rightarrow>
            if v > here then None
            else let addr = here - v in Some (addr, rest, cache_update c addr)
      else if mode < 2 + s_near then
        case varint_decode bs of
          None \<Rightarrow> None
        | Some (v, rest) \<Rightarrow>
            let addr = (near c ! (mode - 2)) + v
            in Some (addr, rest, cache_update c addr)
      else if mode < 2 + s_near + s_same then
        case bs of
          [] \<Rightarrow> None
        | b # rest \<Rightarrow>
            let slot = (mode - 2 - s_near) * 256 + unat b;
                addr = same c ! slot
            in Some (addr, rest, cache_update c addr)
      else None)"

(* ---------- Encoding-shape predicate ---------- *)
(*
  A triple (mode, bs, c') is a valid encoding of addr under cache c and
  here-position `here` if either:
    mode = 0, bs = varint_encode addr @ rest
    mode = 1, addr \<le> here, bs = varint_encode (here - addr) @ rest
    2 \<le> mode < 2 + s_near, near c ! (mode - 2) \<le> addr,
                            bs = varint_encode (addr - near c ! (mode-2)) @ rest
    2 + s_near \<le> mode < 2 + s_near + s_same,
                            same c ! ((mode - 2 - s_near) * 256 + addr mod 256) = addr,
                            addr \<noteq> 0,
                            bs = [word_of_nat (addr mod 256)]
  plus c' = cache_update c addr in every case.

  The encoder's try_better + try_near_modes + try_same_modes choose one of
  these shapes. The decoder expects exactly these shapes for each mode.
*)

definition wf_encoding :: "cache \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> bool" where
  "wf_encoding c addr here mode bs =
     (if mode = 0 then bs = varint_encode addr
      else if mode = 1 then addr \<le> here \<and> bs = varint_encode (here - addr)
      else if mode < 2 + s_near then
        near c ! (mode - 2) \<le> addr
        \<and> bs = varint_encode (addr - near c ! (mode - 2))
      else if mode < 2 + s_near + s_same then
        same c ! ((mode - 2 - s_near) * 256 + addr mod 256) = addr
        \<and> addr \<noteq> 0
        \<and> bs = [word_of_nat (addr mod 256)]
      else False)"

(* Varint-based branches need addr \<le> 2^32; single-byte branches don't. *)
lemma wf_encoding_decodes:
  assumes "wf_encoding c addr here mode bs"
          "addr < 2 ^ 32" "here < 2 ^ 32"
  shows "decode_address c mode here (bs @ rest) = Some (addr, rest, cache_update c addr)"
proof -
  show ?thesis
  proof (cases "mode = 0")
    case True
    then have bs_eq: "bs = varint_encode addr" using assms(1) wf_encoding_def by simp
    show ?thesis
      using True bs_eq assms(2)
      by (simp add: decode_address_def varint_decode_encode)
  next
    case m0_false: False
    show ?thesis
    proof (cases "mode = 1")
      case True
      then have ble: "addr \<le> here" and bs_eq: "bs = varint_encode (here - addr)"
        using assms(1) m0_false by (auto simp: wf_encoding_def)
      have bd: "here - addr < 2 ^ 32" using assms(3) by simp
      have dec: "varint_decode (varint_encode (here - addr) @ rest)
                  = Some (here - addr, rest)"
        using bd by (rule varint_decode_encode)
      have recover: "here - (here - addr) = addr" using ble by simp
      have "\<not> here - addr > here"
        using ble by (cases "here = addr") auto
      show ?thesis
        using True m0_false bs_eq dec recover ble
        by (auto simp add: decode_address_def)
    next
      case m1_false: False
      show ?thesis
      proof (cases "mode < 2 + s_near")
        case True
        then have nle: "near c ! (mode - 2) \<le> addr"
             and bs_eq: "bs = varint_encode (addr - near c ! (mode - 2))"
          using assms(1) m0_false m1_false by (auto simp: wf_encoding_def)
        have bd: "addr - near c ! (mode - 2) < 2 ^ 32" using assms(2) by simp
        have dec: "varint_decode (bs @ rest)
                    = Some (addr - near c ! (mode - 2), rest)"
          using bs_eq bd by (simp add: varint_decode_encode)
        show ?thesis
          using True m0_false m1_false dec nle
          by (auto simp add: decode_address_def)
      next
        case n_false: False
        have "mode < 2 + s_near + s_same"
          using assms(1) m0_false m1_false n_false
          by (auto simp: wf_encoding_def split: if_splits)
        hence mode_lt: "mode < 2 + s_near + s_same" .
        have wf_body: "same c ! ((mode - 2 - s_near) * 256 + addr mod 256) = addr
                       \<and> addr \<noteq> 0
                       \<and> bs = [word_of_nat (addr mod 256)]"
          using assms(1) m0_false m1_false n_false mode_lt
          by (auto simp: wf_encoding_def)
        have slot_eq: "same c ! ((mode - 2 - s_near) * 256 + addr mod 256) = addr"
          using wf_body by simp
        have addr_ne: "addr \<noteq> 0" using wf_body by simp
        have bs_eq: "bs = [word_of_nat (addr mod 256)]" using wf_body by simp
        have b_unat: "unat (word_of_nat (addr mod 256) :: byte) = addr mod 256"
          by (simp add: unat_of_nat_eq)
        show ?thesis
          using m0_false m1_false n_false mode_lt bs_eq slot_eq b_unat
          by (simp add: decode_address_def Let_def)
      qed
    qed
  qed
qed

(* ---------- Encoder outputs satisfy wf_encoding ---------- *)

lemma try_better_cases:
  "try_better b m e = b \<or> try_better b m e = (m, e)"
  by (simp add: try_better_def)

(* try_near_mode either returns the input or a NEAR-shape encoding. *)
lemma try_near_mode_shape:
  assumes "i < s_near"
  shows "try_near_mode c addr i best = best
       \<or> (near c ! i \<le> addr
          \<and> try_near_mode c addr i best
              = (2 + i, varint_encode (addr - near c ! i)))"
  using assms
  by (auto simp: try_near_mode_def try_better_def Let_def)

lemma try_near_modes_preserves_wf:
  assumes "fst best = 0 \<longrightarrow> snd best = varint_encode addr"
          "\<forall>m b. best = (m, b) \<longrightarrow> (m = 0 \<or> wf_encoding c addr here m b)"
          "k \<le> s_near"
  shows "\<forall>m b. try_near_modes c addr k best = (m, b)
             \<longrightarrow> (m = 0 \<or> wf_encoding c addr here m b)"
  using assms
proof (induction k arbitrary: best)
  case 0
  show ?case using 0 by simp
next
  case (Suc k)
  let ?i = "s_near - Suc k"
  have i_lt: "?i < s_near" using Suc.prems(3) by simp
  have shape: "try_near_mode c addr ?i best = best
              \<or> (near c ! ?i \<le> addr
                 \<and> try_near_mode c addr ?i best
                     = (2 + ?i, varint_encode (addr - near c ! ?i)))"
    by (rule try_near_mode_shape[OF i_lt])
  show ?case
  proof (cases "try_near_mode c addr ?i best = best")
    case True
    have "\<forall>m b. try_near_modes c addr k best = (m, b)
               \<longrightarrow> m = 0 \<or> wf_encoding c addr here m b"
      using Suc.IH[OF Suc.prems(1) Suc.prems(2)] Suc.prems(3) by simp
    thus ?thesis using True by simp
  next
    case False
    then obtain bst' where bst'_def:
       "try_near_mode c addr ?i best = bst'"
       "near c ! ?i \<le> addr"
       "bst' = (2 + ?i, varint_encode (addr - near c ! ?i))"
      using shape by auto
    have i_ge: "?i < s_near" using i_lt .
    have mode_lt_near: "2 + ?i < 2 + s_near" using i_ge by simp
    have mode_ne_0: "(2::nat) + ?i \<noteq> 0" by simp
    have mode_ne_1: "(2::nat) + ?i \<noteq> 1" by simp
    have wf_bst': "wf_encoding c addr here (fst bst') (snd bst')"
      using bst'_def mode_lt_near mode_ne_0 mode_ne_1
      by (auto simp: wf_encoding_def)
    have prem1: "fst bst' = 0 \<longrightarrow> snd bst' = varint_encode addr"
      using bst'_def by simp
    have prem2: "\<forall>m b. bst' = (m, b) \<longrightarrow> m = 0 \<or> wf_encoding c addr here m b"
      using wf_bst' bst'_def by auto
    show ?thesis
      using Suc.IH[OF prem1 prem2] Suc.prems(3) bst'_def
      by simp
  qed
qed

(*
  When the `best` has mode 0 and enc-0 as its bytes, iterating try_near_modes
  either preserves this invariant or switches to a non-mode-0 choice. This
  lets us carry the "mode 0 \<Longrightarrow> snd = varint_encode addr" invariant along
  the chain.
*)
lemma try_near_modes_preserves_snd0:
  assumes "fst best = 0 \<longrightarrow> snd best = varint_encode addr"
          "k \<le> s_near"
  shows "fst (try_near_modes c addr k best) = 0
       \<longrightarrow> snd (try_near_modes c addr k best) = varint_encode addr"
  using assms
proof (induction k arbitrary: best)
  case 0 then show ?case by simp
next
  case (Suc k)
  let ?i = "s_near - Suc k"
  have shape: "try_near_mode c addr ?i best = best
              \<or> try_near_mode c addr ?i best
                   = (2 + ?i, varint_encode (addr - near c ! ?i))"
    unfolding try_near_mode_def Let_def
    by (auto simp: try_better_def)
  let ?b' = "try_near_mode c addr ?i best"
  have prem1: "fst ?b' = 0 \<longrightarrow> snd ?b' = varint_encode addr"
    using shape Suc.prems(1) by auto
  show ?case
    using Suc.IH[OF prem1] Suc.prems(2) by simp
qed

lemma try_same_modes_preserves_snd0:
  assumes "fst best = 0 \<longrightarrow> snd best = varint_encode addr"
          "k \<le> s_same"
  shows "fst (try_same_modes c addr k best) = 0
       \<longrightarrow> snd (try_same_modes c addr k best) = varint_encode addr"
  using assms
proof (induction k arbitrary: best)
  case 0 then show ?case by simp
next
  case (Suc k)
  let ?bank = "s_same - Suc k"
  let ?b' = "try_same_mode c addr ?bank best"
  have shape: "?b' = best
              \<or> ?b' = (2 + s_near + ?bank, [word_of_nat (addr mod 256)])"
    unfolding try_same_mode_def Let_def
    by (auto simp: try_better_def)
  have prem1: "fst ?b' = 0 \<longrightarrow> snd ?b' = varint_encode addr"
    using shape Suc.prems(1) by auto
  show ?case
    using Suc.IH[OF prem1] Suc.prems(2) by simp
qed

lemma try_same_modes_preserves_wf:
  assumes "fst best = 0 \<longrightarrow> snd best = varint_encode addr"
          "\<forall>m b. best = (m, b) \<longrightarrow> (m = 0 \<or> wf_encoding c addr here m b)"
          "k \<le> s_same"
  shows "\<forall>m b. try_same_modes c addr k best = (m, b)
             \<longrightarrow> (m = 0 \<or> wf_encoding c addr here m b)"
  using assms
proof (induction k arbitrary: best)
  case 0
  show ?case using 0 by simp
next
  case (Suc k)
  let ?bank = "s_same - Suc k"
  let ?slot = "?bank * 256 + addr mod 256"
  let ?b' = "try_same_mode c addr ?bank best"
  have ?case if not_taken: "?b' = best"
    using Suc.IH[OF Suc.prems(1) Suc.prems(2)] Suc.prems(3) not_taken by simp
  moreover have ?case if taken: "?b' \<noteq> best"
  proof -
    from taken have cond: "same c ! ?slot = addr \<and> addr \<noteq> 0"
      unfolding try_same_mode_def Let_def
      by (auto split: if_splits simp: try_better_def)
    from taken have better:
       "?b' = (2 + s_near + ?bank, [word_of_nat (addr mod 256)])
       \<or> ?b' = best"
      unfolding try_same_mode_def Let_def
      by (auto simp: try_better_def split: if_splits)
    from better taken have bdef: "?b' = (2 + s_near + ?bank, [word_of_nat (addr mod 256)])"
      by blast
    have bank_lt: "?bank < s_same" using Suc.prems(3) by simp
    have mode_lt: "2 + s_near + ?bank < 2 + s_near + s_same" using bank_lt by simp
    have wf_b': "wf_encoding c addr here (fst ?b') (snd ?b')"
      using bdef cond mode_lt by (auto simp: wf_encoding_def)
    have prem1: "fst ?b' = 0 \<longrightarrow> snd ?b' = varint_encode addr"
      using bdef by simp
    have prem2: "\<forall>m b. ?b' = (m, b) \<longrightarrow> m = 0 \<or> wf_encoding c addr here m b"
      using wf_b' by auto
    show ?thesis
      using Suc.IH[OF prem1 prem2] Suc.prems(3) bdef
      by simp
  qed
  ultimately show ?case by blast
qed

(*
  encode_address picks a mode/encoding that is well-formed against the
  input cache. Combined with the wf_encoding_decodes lemma above, this
  gives the full encode/decode inversion.
*)
lemma encode_address_wf:
  assumes "addr < 2 ^ 32" "here < 2 ^ 32"
  shows "\<exists>mode bs. encode_address c addr here = (mode, bs, cache_update c addr)
                 \<and> wf_encoding c addr here mode bs"
proof -
  let ?enc0 = "varint_encode addr"
  let ?best0 = "(0 :: nat, ?enc0)"
  let ?best1 =
    "(if here > addr
      then try_better ?best0 1 (varint_encode (here - addr))
      else ?best0)"
  let ?best2 = "try_near_modes c addr s_near ?best1"
  let ?best3 = "try_same_modes c addr s_same ?best2"

  have ea: "encode_address c addr here = (fst ?best3, snd ?best3, cache_update c addr)"
    by (simp add: encode_address_def Let_def)

  (* best1 is either best0 (mode 0) or a mode-1 entry. *)
  have wf1_cases: "?best1 = ?best0 \<or> ?best1 = (1, varint_encode (here - addr))"
  proof (cases "here > addr")
    case True
    then show ?thesis
      using try_better_cases by metis
  next
    case False then show ?thesis by simp
  qed

  have wf_best1_snd: "fst ?best1 = 0 \<longrightarrow> snd ?best1 = varint_encode addr"
    using wf1_cases by auto

  have wf_best1_body:
      "\<forall>m b. ?best1 = (m, b) \<longrightarrow> m = 0 \<or> wf_encoding c addr here m b"
  proof (intro allI impI)
    fix m b
    assume eq: "?best1 = (m, b)"
    show "m = 0 \<or> wf_encoding c addr here m b"
    proof (cases "here > addr")
      case True
      with wf1_cases have "?best1 = ?best0 \<or> ?best1 = (1, varint_encode (here - addr))"
        by blast
      then consider (a) "?best1 = ?best0" | (b) "?best1 = (1, varint_encode (here - addr))"
        by blast
      then show ?thesis
      proof cases
        case a with eq show ?thesis by auto
      next
        case b
        have ble: "addr \<le> here" using True by simp
        have wf_b: "wf_encoding c addr here 1 (varint_encode (here - addr))"
          using ble by (simp add: wf_encoding_def)
        from b eq have "(m, b) = (1, varint_encode (here - addr))" by simp
        then show ?thesis using wf_b by auto
      qed
    next
      case False
      then have "?best1 = ?best0" by simp
      with eq show ?thesis by auto
    qed
  qed

  have wf_best2_invariant:
    "\<forall>m b. ?best2 = (m, b) \<longrightarrow> m = 0 \<or> wf_encoding c addr here m b"
    using try_near_modes_preserves_wf[OF wf_best1_snd wf_best1_body le_refl] .

  have best2_snd: "fst ?best2 = 0 \<longrightarrow> snd ?best2 = varint_encode addr"
    using try_near_modes_preserves_snd0[OF wf_best1_snd le_refl] .

  have wf_best3_invariant:
    "\<forall>m b. ?best3 = (m, b) \<longrightarrow> m = 0 \<or> wf_encoding c addr here m b"
    using try_same_modes_preserves_wf[OF best2_snd wf_best2_invariant le_refl] .

  have best3_snd: "fst ?best3 = 0 \<longrightarrow> snd ?best3 = varint_encode addr"
    using try_same_modes_preserves_snd0[OF best2_snd le_refl] .

  obtain mode bs where split: "?best3 = (mode, bs)" by (cases ?best3) auto

  have wf_result: "mode = 0 \<or> wf_encoding c addr here mode bs"
    using wf_best3_invariant split by auto

  have mode0_eq: "mode = 0 \<longrightarrow> bs = varint_encode addr"
    using best3_snd split by auto

  have wf_full: "wf_encoding c addr here mode bs"
  proof (cases "mode = 0")
    case True
    then have "bs = varint_encode addr" using mode0_eq by simp
    then show ?thesis using True by (simp add: wf_encoding_def)
  next
    case False
    then show ?thesis using wf_result by simp
  qed

  show ?thesis
    using ea split wf_full by auto
qed

(* ---------- Phase A.2 main goal: encode/decode inversion ---------- *)
lemma encode_decode_address:
  assumes "addr < 2 ^ 32" "here < 2 ^ 32"
  shows
    "let (mode, bs, c') = encode_address c addr here
     in decode_address c mode here (bs @ rest) = Some (addr, rest, c')"
proof -
  obtain mode bs where
    ea: "encode_address c addr here = (mode, bs, cache_update c addr)" and
    wf: "wf_encoding c addr here mode bs"
    using encode_address_wf[OF assms] by blast
  show ?thesis
    using ea wf_encoding_decodes[OF wf assms] by simp
qed

(* Helper: if best's mode < num_modes, try_near_mode preserves that. *)
lemma try_near_mode_mode_bound:
  assumes "fst best < num_modes" "i < s_near"
  shows "fst (try_near_mode c addr i best) < num_modes"
  using assms
  unfolding try_near_mode_def Let_def try_better_def
  by (auto simp: num_modes_def s_near_def s_same_def)

lemma try_near_modes_mode_bound:
  assumes "fst best < num_modes" "k \<le> s_near"
  shows "fst (try_near_modes c addr k best) < num_modes"
  using assms
proof (induction k arbitrary: best)
  case 0 then show ?case by simp
next
  case (Suc k)
  let ?i = "s_near - Suc k"
  have "?i < s_near" using Suc.prems(2) by simp
  then have "fst (try_near_mode c addr ?i best) < num_modes"
    using try_near_mode_mode_bound[OF Suc.prems(1)] by simp
  then show ?case using Suc.IH Suc.prems(2) by simp
qed

lemma try_same_mode_mode_bound:
  assumes "fst best < num_modes" "bank < s_same"
  shows "fst (try_same_mode c addr bank best) < num_modes"
  using assms
  unfolding try_same_mode_def Let_def try_better_def
  by (auto simp: num_modes_def s_near_def s_same_def)

lemma try_same_modes_mode_bound:
  assumes "fst best < num_modes" "k \<le> s_same"
  shows "fst (try_same_modes c addr k best) < num_modes"
  using assms
proof (induction k arbitrary: best)
  case 0 then show ?case by simp
next
  case (Suc k)
  let ?bank = "s_same - Suc k"
  have "?bank < s_same" using Suc.prems(2) by simp
  then have "fst (try_same_mode c addr ?bank best) < num_modes"
    using try_same_mode_mode_bound[OF Suc.prems(1)] by simp
  then show ?case using Suc.IH Suc.prems(2) by simp
qed

(* Mode returned by encode_address is always a valid one (< num_modes). *)
lemma encode_address_mode_bound:
  "fst (encode_address c addr here) < num_modes"
proof -
  let ?best1 =
    "(if here > addr
      then try_better (0 :: nat, varint_encode addr) 1 (varint_encode (here - addr))
      else (0, varint_encode addr))"
  have b0: "fst ((0 :: nat, varint_encode addr)) < num_modes"
    by (simp add: num_modes_def)
  have b1: "fst ?best1 < num_modes"
    unfolding try_better_def by (auto simp: num_modes_def)
  let ?best2 = "try_near_modes c addr s_near ?best1"
  have b2: "fst ?best2 < num_modes"
    using try_near_modes_mode_bound[OF b1 le_refl] .
  let ?best3 = "try_same_modes c addr s_same ?best2"
  have b3: "fst ?best3 < num_modes"
    using try_same_modes_mode_bound[OF b2 le_refl] .
  show ?thesis
    using b3 by (simp add: encode_address_def Let_def)
qed

end
