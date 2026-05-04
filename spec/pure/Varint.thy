(*
  VCDIFF base-128 varint codec (RFC 3284).

  Wire format: big-endian groups of 7 bits per byte. The high (0x80) bit of
  each byte is 1 to mean "more groups follow", 0 to mean "last group".
  Maximum 5 bytes — the 5th byte's accumulated value must fit in 32 bits, or
  the decoder rejects the input.

  This theory mirrors the C in `encoder/vcdiff_enc.c` (write_varint,
  varint_size) and `decoder/vcdiff_dec.c` (read_varint) as pure functions
  over `byte list`. Indices live at the AutoCorres refinement layer; here
  the decoder just returns the unconsumed tail of the byte list.
*)
theory Varint
  imports Bytes
begin

unbundle bit_operations_syntax

(* ---------- Encoding ---------- *)

(* Collect base-128 digits of n in big-endian order (most significant first).
   Returns [] for n = 0. Each digit is in [0, 128). *)
function to_base128 :: "nat \<Rightarrow> nat list" where
  "to_base128 n =
     (if n = 0 then []
      else to_base128 (n div 128) @ [n mod 128])"
  by pat_completeness auto
termination by (relation "measure id") auto

declare to_base128.simps [simp del]

lemma to_base128_zero [simp]: "to_base128 0 = []"
  by (simp add: to_base128.simps)

lemma to_base128_nonzero:
  "n > 0 \<Longrightarrow> to_base128 n = to_base128 (n div 128) @ [n mod 128]"
  by (simp add: to_base128.simps)

lemma to_base128_digit_bound:
  "\<forall>d \<in> set (to_base128 n). d < 128"
proof (induction n rule: to_base128.induct)
  case (1 n)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis by simp
  next
    case False
    hence pos: "n > 0" by simp
    have rec: "to_base128 n = to_base128 (n div 128) @ [n mod 128]"
      by (rule to_base128_nonzero[OF pos])
    have "n mod 128 < 128" by simp
    moreover have "\<forall>d \<in> set (to_base128 (n div 128)). d < 128"
      using 1 False by blast
    ultimately show ?thesis by (simp add: rec)
  qed
qed

(* Number of base-128 digits: 0 for n = 0, else ceiling(log_128 (n+1)). *)
function num_digits :: "nat \<Rightarrow> nat" where
  "num_digits n = (if n = 0 then 0 else num_digits (n div 128) + 1)"
  by pat_completeness auto
termination by (relation "measure id") auto

declare num_digits.simps [simp del]

lemma num_digits_zero [simp]: "num_digits 0 = 0"
  by (simp add: num_digits.simps)

lemma num_digits_nonzero:
  "n > 0 \<Longrightarrow> num_digits n = num_digits (n div 128) + 1"
  by (simp add: num_digits.simps)

lemma to_base128_length [simp]:
  "length (to_base128 n) = num_digits n"
proof (induction n rule: to_base128.induct)
  case (1 n)
  show ?case
  proof (cases "n = 0")
    case True then show ?thesis by simp
  next
    case False
    hence pos: "n > 0" by simp
    have rec: "to_base128 n = to_base128 (n div 128) @ [n mod 128]"
      by (rule to_base128_nonzero[OF pos])
    have ih: "length (to_base128 (n div 128)) = num_digits (n div 128)"
      using 1 False by blast
    show ?thesis
      by (simp add: rec ih num_digits_nonzero[OF pos])
  qed
qed

(* General bound: num_digits n \<le> k whenever n < 128^k. Proved by
   induction on k; k = 5 is the VCDIFF cap. *)
lemma num_digits_le:
  "n < 128 ^ k \<Longrightarrow> num_digits n \<le> k"
proof (induction k arbitrary: n)
  case 0
  then show ?case by (simp add: num_digits.simps)
next
  case (Suc k)
  show ?case
  proof (cases "n = 0")
    case True then show ?thesis by simp
  next
    case False
    hence pos: "n > 0" by simp
    have "n div 128 < 128 ^ k"
      using Suc.prems by (simp add: less_mult_imp_div_less)
    hence ih: "num_digits (n div 128) \<le> k" using Suc.IH by blast
    show ?thesis using ih by (simp add: num_digits_nonzero[OF pos])
  qed
qed

lemma num_digits_le_5:
  "n < 2 ^ 35 \<Longrightarrow> num_digits n \<le> 5"
  using num_digits_le[where k = 5] by simp

(* Set the continuation (0x80) bit on all list elements except the last. *)
fun set_cont_bits :: "byte list \<Rightarrow> byte list" where
  "set_cont_bits [] = []"
| "set_cont_bits [b] = [b]"
| "set_cont_bits (b # b' # rest) = (b OR 0x80) # set_cont_bits (b' # rest)"

lemma set_cont_bits_length [simp]:
  "length (set_cont_bits bs) = length bs"
  by (induction bs rule: set_cont_bits.induct) auto

lemma set_cont_bits_empty_iff [simp]:
  "set_cont_bits bs = [] \<longleftrightarrow> bs = []"
  by (cases bs rule: set_cont_bits.cases) auto

lemma to_base128_empty_iff [simp]:
  "to_base128 n = [] \<longleftrightarrow> n = 0"
proof (cases "n = 0")
  case True then show ?thesis by simp
next
  case False hence "n > 0" by simp
  thus ?thesis by (simp add: to_base128_nonzero)
qed

(* Encode a natural number as a VCDIFF varint. For n = 0 this is the single
   byte [0x00]; otherwise it's the base-128 big-endian digit list with
   continuation bits on all but the final byte. *)
definition varint_encode :: "nat \<Rightarrow> byte list" where
  "varint_encode n =
     (if n = 0 then [0]
      else set_cont_bits (map (\<lambda>d. word_of_nat d) (to_base128 n)))"

(* The encoded size matches the C's varint_size helper: 1 for n = 0, else
   num_digits n. *)
definition varint_size :: "nat \<Rightarrow> nat" where
  "varint_size n = (if n = 0 then 1 else num_digits n)"

lemma varint_encode_length [simp]:
  "length (varint_encode n) = varint_size n"
  by (simp add: varint_encode_def varint_size_def)

(* Encoder never produces the empty list. *)
lemma varint_encode_nonempty: "varint_encode n \<noteq> []"
  by (cases "n = 0") (simp_all add: varint_encode_def)

(* ---------- Decoding ---------- *)

(* Bounded varint decoder. Consumes at most `fuel` bytes; for VCDIFF we set
   fuel = 5. Rejects if the accumulated value does not fit in 32 bits — the
   C's overflow check `(v & 0xFE000000) != 0` on iteration 4 is equivalent
   to requiring the final result < 2^32. *)
fun varint_decode_loop :: "nat \<Rightarrow> nat \<Rightarrow> byte list \<Rightarrow> (nat \<times> byte list) option" where
  "varint_decode_loop 0 acc bs = None"
| "varint_decode_loop (Suc fuel) acc [] = None"
| "varint_decode_loop (Suc fuel) acc (b # rest) =
     (let acc' = acc * 128 + unat (b AND 0x7F) in
      if b AND 0x80 = 0 then
        (if acc' < 2 ^ 32 then Some (acc', rest) else None)
      else
        varint_decode_loop fuel acc' rest)"

(* Top-level decoder: 5-byte bound per RFC 3284 / xdelta3 default. *)
definition varint_decode :: "byte list \<Rightarrow> (nat \<times> byte list) option" where
  "varint_decode bs = varint_decode_loop 5 0 bs"

(* ---------- Base-128 digit arithmetic ---------- *)

(* Interpret a big-endian digit list as a natural number. *)
fun from_base128_acc :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "from_base128_acc acc [] = acc"
| "from_base128_acc acc (d # ds) = from_base128_acc (acc * 128 + d) ds"

definition from_base128 :: "nat list \<Rightarrow> nat" where
  "from_base128 ds = from_base128_acc 0 ds"

lemma from_base128_acc_append:
  "from_base128_acc acc (xs @ ys) = from_base128_acc (from_base128_acc acc xs) ys"
  by (induction xs arbitrary: acc) auto

lemma from_base128_acc_single:
  "from_base128_acc acc [d] = acc * 128 + d"
  by simp

lemma from_base128_to_base128:
  "from_base128 (to_base128 n) = n"
proof (induction n rule: to_base128.induct)
  case (1 n)
  show ?case
  proof (cases "n = 0")
    case True then show ?thesis by (simp add: from_base128_def)
  next
    case False
    hence pos: "n > 0" by simp
    have rec: "to_base128 n = to_base128 (n div 128) @ [n mod 128]"
      by (rule to_base128_nonzero[OF pos])
    have ih: "from_base128 (to_base128 (n div 128)) = n div 128"
      using 1 False by blast
    have "from_base128 (to_base128 n)
          = from_base128_acc 0 (to_base128 (n div 128) @ [n mod 128])"
      by (simp add: rec from_base128_def)
    also have "\<dots> = from_base128_acc
                      (from_base128_acc 0 (to_base128 (n div 128)))
                      [n mod 128]"
      by (rule from_base128_acc_append)
    also have "\<dots> = (from_base128 (to_base128 (n div 128))) * 128 + n mod 128"
      by (simp add: from_base128_def)
    also have "\<dots> = n div 128 * 128 + n mod 128" by (simp add: ih)
    also have "\<dots> = n" by simp
    finally show ?thesis .
  qed
qed

(* Bound digits produce bounded accumulator. *)
lemma from_base128_acc_bound:
  assumes "\<forall>d \<in> set ds. d < 128"
  shows   "from_base128_acc acc ds < (acc + 1) * 128 ^ length ds"
  using assms
proof (induction ds arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons d ds)
  from Cons.prems have d_bd: "d < 128" and rest_bd: "\<forall>x\<in>set ds. x < 128" by auto
  have "from_base128_acc acc (d # ds) = from_base128_acc (acc * 128 + d) ds"
    by simp
  also have "\<dots> < (acc * 128 + d + 1) * 128 ^ length ds"
    using Cons.IH[OF rest_bd, of "acc * 128 + d"] by simp
  also have "\<dots> \<le> (acc + 1) * 128 ^ length (d # ds)"
    using d_bd by (simp add: algebra_simps)
  finally show ?case .
qed

lemma from_base128_bound:
  assumes "\<forall>d \<in> set ds. d < 128"
  shows   "from_base128 ds < 128 ^ length ds"
  using from_base128_acc_bound[OF assms, of 0] by (simp add: from_base128_def)

(* ---------- Byte-level AND/OR lemmas for digits < 128 ---------- *)

lemma digit_unat_of_nat [simp]:
  fixes d :: nat
  assumes "d < 128"
  shows "unat (word_of_nat d :: byte) = d"
  using assms by (simp add: unat_of_nat_eq)

(* Byte-level lemmas. The 7-bit bound d < 128 translates to "bit 7 is
   clear" via bit_word_of_nat_iff. *)

lemma digit_byte_le_127:
  fixes d :: nat
  assumes "d < 128"
  shows "(word_of_nat d :: byte) \<le> 0x7F"
  using assms by (simp add: word_le_nat_alt unat_of_nat_eq)

lemma digit_byte_and_7F:
  fixes d :: nat
  assumes "d < 128"
  shows "(word_of_nat d :: byte) AND 0x7F = word_of_nat d"
proof -
  have "(word_of_nat d :: byte) \<le> mask 7"
    using digit_byte_le_127[OF assms] by (simp add: mask_eq_decr_exp)
  hence "(word_of_nat d :: byte) AND mask 7 = word_of_nat d"
    by (rule and_mask_eq_iff_le_mask[THEN iffD2])
  thus ?thesis by (simp add: mask_eq_decr_exp)
qed

lemma digit_byte_and_80:
  fixes d :: nat
  assumes "d < 128"
  shows "(word_of_nat d :: byte) AND 0x80 = 0"
proof -
  have le_mask: "(word_of_nat d :: byte) \<le> mask 7"
    using digit_byte_le_127[OF assms] by (simp add: mask_eq_decr_exp)
  have eq_80: "(NOT (mask 7) :: byte) = 0x80"
    by (simp add: mask_eq_decr_exp)
  have "(word_of_nat d :: byte) AND NOT (mask 7)
          = ((word_of_nat d :: byte) AND mask 7) AND NOT (mask 7)"
    using le_mask
    by (simp add: and_mask_eq_iff_le_mask[THEN iffD2])
  also have "\<dots> = 0" by (rule NOT_mask_AND_mask)
  finally show ?thesis using eq_80 by simp
qed

lemma digit_byte_or_80_and_7F:
  fixes d :: nat
  assumes "d < 128"
  shows "((word_of_nat d :: byte) OR 0x80) AND 0x7F = word_of_nat d"
proof -
  have "((word_of_nat d :: byte) OR 0x80) AND 0x7F
          = ((word_of_nat d :: byte) AND 0x7F) OR (0x80 AND 0x7F)"
    by (simp add: word_ao_dist)
  also have "\<dots> = word_of_nat d OR 0"
    by (simp add: digit_byte_and_7F[OF assms])
  finally show ?thesis by simp
qed

lemma digit_byte_or_80_msb:
  fixes d :: nat
  assumes "d < 128"
  shows "((word_of_nat d :: byte) OR 0x80) AND 0x80 \<noteq> 0"
proof -
  have "((word_of_nat d :: byte) OR 0x80) AND 0x80
          = ((word_of_nat d :: byte) AND 0x80) OR (0x80 AND 0x80)"
    by (simp add: word_ao_dist)
  also have "\<dots> = (0 :: byte) OR 0x80"
    by (simp add: digit_byte_and_80[OF assms])
  also have "\<dots> = 0x80" by simp
  finally show ?thesis by simp
qed

(* ---------- Decoder main lemma ---------- *)

(* Unrolling of set_cont_bits of a single-byte list. *)
lemma set_cont_bits_singleton [simp]:
  "set_cont_bits [b] = [b]"
  by simp

(* set_cont_bits (x # y # ys) = (x OR 0x80) # set_cont_bits (y # ys). *)
lemma set_cont_bits_cons_cons:
  "set_cont_bits (x # y # ys) = (x OR 0x80) # set_cont_bits (y # ys)"
  by simp

(* Key lemma: decoding the cont-bit-set encoding of a non-empty digit list
   with all digits < 128 accumulates to the base-128 value. Proof is by
   induction on the digit list: the singleton case exercises the no-cont
   branch of the decoder, the cons-cons case exercises the continuation
   branch. *)
lemma varint_decode_loop_on_encoded:
  assumes "ds \<noteq> []"
          "\<forall>d \<in> set ds. d < 128"
          "length ds \<le> fuel"
          "from_base128_acc acc ds < 2 ^ 32"
  shows
    "varint_decode_loop fuel acc
       (set_cont_bits (map word_of_nat ds) @ rest)
     = Some (from_base128_acc acc ds, rest)"
  using assms
proof (induction ds arbitrary: acc fuel)
  case Nil then show ?case by simp
next
  case (Cons d ds)
  from Cons.prems have d_lt: "d < 128" by simp
  from Cons.prems have fuel_pos: "fuel > 0" by (cases fuel) auto
  then obtain k where fuel_eq: "fuel = Suc k" by (cases fuel) auto
  show ?case
  proof (cases ds)
    case Nil
    \<comment> \<open>Single-digit case. Decoder reads [word_of_nat d], bit 7 is clear,
        acc' = acc * 128 + d, which equals from_base128_acc acc [d] and
        must be < 2^32 by the premise.\<close>
    have "set_cont_bits (map word_of_nat (d # ds))
            = [word_of_nat d :: byte]"
      by (simp add: Nil)
    hence decode_input:
      "set_cont_bits (map word_of_nat (d # ds)) @ rest
        = (word_of_nat d :: byte) # rest" by simp
    have acc_eq: "acc * 128 + unat ((word_of_nat d :: byte) AND 0x7F)
                  = from_base128_acc acc (d # ds)"
      using d_lt by (simp add: digit_byte_and_7F Nil)
    have msb_clr: "((word_of_nat d :: byte) AND 0x80) = 0"
      using digit_byte_and_80[OF d_lt] .
    have bound: "acc * 128 + unat ((word_of_nat d :: byte) AND 0x7F) < 2 ^ 32"
      using Cons.prems(4) acc_eq by simp
    show ?thesis
      using fuel_eq decode_input acc_eq msb_clr bound
      by (simp add: Let_def)
  next
    case (Cons d' ds')
    \<comment> \<open>Cons-cons case. Decoder reads (word_of_nat d OR 0x80); bit 7 set;
        recurse with acc' = acc * 128 + d on the remaining fuel.\<close>
    have expand: "set_cont_bits (map word_of_nat (d # ds))
                  = ((word_of_nat d :: byte) OR 0x80)
                      # set_cont_bits (map word_of_nat ds)"
      using Cons by (simp add: set_cont_bits_cons_cons)
    have msb_set: "(((word_of_nat d :: byte) OR 0x80) AND 0x80) \<noteq> 0"
      using digit_byte_or_80_msb[OF d_lt] .
    have and_7F: "(((word_of_nat d :: byte) OR 0x80) AND 0x7F) = word_of_nat d"
      using digit_byte_or_80_and_7F[OF d_lt] .
    let ?acc' = "acc * 128 + d"
    have unat_and: "unat (((word_of_nat d :: byte) OR 0x80) AND 0x7F) = d"
      using and_7F d_lt by (simp add: digit_unat_of_nat)
    have ds_nonempty: "ds \<noteq> []" using Cons by simp
    have ds_bd: "\<forall>x \<in> set ds. x < 128" using Cons.prems(2) by simp
    have len_le: "length ds \<le> k" using Cons.prems(3) fuel_eq by simp
    have acc_bound: "from_base128_acc ?acc' ds < 2 ^ 32"
      using Cons.prems(4) by simp
    have IH_applied:
      "varint_decode_loop k ?acc'
         (set_cont_bits (map word_of_nat ds) @ rest)
       = Some (from_base128_acc ?acc' ds, rest)"
      using Cons.IH[OF ds_nonempty ds_bd len_le acc_bound] .
    show ?thesis
      using fuel_eq expand msb_set unat_and IH_applied
      by (simp add: Let_def)
  qed
qed

(* n = 0 case: varint_encode 0 = [0x00]. *)
lemma varint_decode_loop_zero:
  "fuel > 0 \<Longrightarrow> varint_decode_loop fuel 0 ((0 :: byte) # rest) = Some (0, rest)"
  by (cases fuel) (simp_all add: Let_def)

(* Final theorem. *)
lemma varint_decode_encode:
  assumes "n < 2 ^ 32"
  shows "varint_decode (varint_encode n @ rest) = Some (n, rest)"
proof (cases "n = 0")
  case True
  then show ?thesis
    by (simp add: varint_encode_def varint_decode_def varint_decode_loop_zero)
next
  case False
  hence pos: "n > 0" by simp
  let ?ds = "to_base128 n"
  have ds_nonempty: "?ds \<noteq> []" using pos by simp
  have ds_bound: "\<forall>d \<in> set ?ds. d < 128" by (rule to_base128_digit_bound)
  have "n < 2 ^ 35" using assms by simp
  hence len_le: "length ?ds \<le> 5"
    using num_digits_le_5 by simp
  have acc_eq_n: "from_base128_acc 0 ?ds = n"
    using from_base128_to_base128[of n]
    by (simp add: from_base128_def)
  show ?thesis
    using assms ds_nonempty ds_bound len_le
    by (simp add: varint_encode_def varint_decode_def False
                  varint_decode_loop_on_encoded[where acc = 0 and ds = ?ds,
                    OF ds_nonempty ds_bound len_le]
                  acc_eq_n)
qed

(* ---------- Bit-arithmetic helper for the refinement layer ---------- *)

(*
  The C's per-iteration step `v ← (v << 7) | (b & 0x7F)` equals, in
  natural-number arithmetic, `v * 128 + (b & 0x7F)` — provided v fits in
  25 bits (so the shift doesn't overflow in 32-bit word arithmetic).

  This lemma lives here rather than in the refinement session because
  it's a pure bit-arithmetic statement (no heap, no monad). The
  refinement invariant needs it to relate the C's word accumulator to
  varint_decode_loop's nat accumulator.
*)
lemma varint_acc_step:
  fixes v :: "32 word" and b :: "8 word"
  assumes "unat v < 2 ^ 25"
  shows "unat ((v << 7) OR UCAST(8 \<rightarrow> 32) (b AND 0x7F))
       = unat v * 128 + unat (b AND 0x7F)"
proof -
  let ?mb = "UCAST(8 \<rightarrow> 32) (b AND 0x7F)"
  have mask_bd: "unat (b AND 0x7F :: 8 word) < 128"
  proof -
    have "b AND 0x7F \<le> 0x7F" by (simp add: word_and_le1)
    hence "unat (b AND 0x7F) \<le> 127" by (simp add: word_le_nat_alt)
    thus ?thesis by simp
  qed
  have ucast_eq: "unat ?mb = unat (b AND 0x7F)"
    by (simp add: unat_ucast_upcast is_up)
  have shift_eq: "unat (v << 7) = unat v * 128"
  proof -
    have step1: "unat (v << 7) = unat v * 128 mod 2 ^ 32"
      by (simp add: shiftl_t2n unat_word_ariths(2) mult.commute)
    have "unat v * 128 < 2 ^ 32" using assms by simp
    hence "unat v * 128 mod 2 ^ 32 = unat v * 128" by simp
    thus ?thesis using step1 by simp
  qed
  (* The AND = 0 step: (v << 7) has zeros in low 7 bits; (b AND 0x7F) has
     only low 7 bits set. *)
  have disjoint: "(v << 7) AND ?mb = 0"
    by (intro word_eqI) (auto simp: bit_simps)
  (* word_plus_and_or: (x AND y) + (x OR y) = x + y. With disjoint = 0:
     x + y = x OR y. *)
  have sum_eq: "(v << 7) + ?mb = (v << 7) OR ?mb"
    using disjoint by (metis add.left_neutral word_plus_and_or)
  have no_overflow: "unat (v << 7) + unat ?mb < 2 ^ 32"
    using assms shift_eq ucast_eq mask_bd by simp
  have "unat ((v << 7) + ?mb) = unat (v << 7) + unat ?mb"
    using no_overflow by (simp add: unat_plus_if_size word_size)
  thus ?thesis
    using sum_eq shift_eq ucast_eq by simp
qed

(*
  varint_decode_loop with no fuel returns None.
*)
lemma varint_decode_loop_no_fuel:
  "varint_decode_loop 0 acc bs = None"
  by simp

(*
  The C's overflow check `(v & 0xFE000000) != 0` fires exactly when the
  accumulator v no longer fits in 25 bits — i.e. the next step
  `v * 128 + (b & 0x7F)` would exceed 2^32. Used by read_varint'_spec.
*)
lemma varint_overflow_check_nat:
  fixes v :: "32 word"
  shows "(v AND 0xFE000000 = 0) \<longleftrightarrow> unat v < 2 ^ 25"
proof -
  have not_mask: "(NOT (mask 25) :: 32 word) = 0xFE000000"
    by (simp add: mask_eq_decr_exp)
  have split: "(v AND mask 25) + (v AND NOT (mask 25)) = v"
    by (rule word_plus_and_or_coroll2)
  have "(v AND 0xFE000000 = 0) \<longleftrightarrow> v AND NOT (mask 25) = 0"
    using not_mask by simp
  also have "\<dots> \<longleftrightarrow> v AND mask 25 = v"
  proof
    assume "v AND NOT (mask 25) = 0"
    with split show "v AND mask 25 = v" by simp
  next
    assume eq: "v AND mask 25 = v"
    have "v + (v AND NOT (mask 25)) = v" using split eq by simp
    thus "v AND NOT (mask 25) = 0" by simp
  qed
  also have "\<dots> \<longleftrightarrow> v \<le> mask 25"
    by (rule and_mask_eq_iff_le_mask)
  also have "\<dots> \<longleftrightarrow> v < 2 ^ 25"
    using le_mask_iff_lt_2n[of 25 v] by simp
  also have "\<dots> \<longleftrightarrow> unat v < 2 ^ 25"
    by (simp add: word_less_nat_alt)
  finally show ?thesis .
qed

(*
  varint_decode_loop is monotone in fuel in the sense that if the decode
  succeeds with fuel n, it succeeds with any fuel >= n giving the same
  result. Useful for the invariant: at iteration i in the C, the loop
  has fuel (5 - i) remaining, and at iteration 0, fuel = 5, but the
  accumulator state matches fuel = (5 - i) starting from accumulator v.
*)
lemma varint_decode_loop_fuel_mono:
  assumes "varint_decode_loop n acc bs = Some (v, rest)"
      and "n \<le> m"
  shows "varint_decode_loop m acc bs = Some (v, rest)"
  using assms
proof (induction n arbitrary: acc bs m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain m' where m_eq: "m = Suc m'" "n \<le> m'"
    using Suc.prems(2) by (cases m) auto
  show ?case
  proof (cases bs)
    case Nil
    then show ?thesis using Suc.prems by simp
  next
    case (Cons b rest')
    let ?acc' = "acc * 128 + unat (b AND 0x7F)"
    show ?thesis
    proof (cases "b AND 0x80 = 0")
      case True
      then show ?thesis using Suc.prems Cons m_eq by simp
    next
      case False
      then have "varint_decode_loop n ?acc' rest' = Some (v, rest)"
        using Suc.prems Cons by (simp add: Let_def)
      hence "varint_decode_loop m' ?acc' rest' = Some (v, rest)"
        using Suc.IH m_eq by blast
      thus ?thesis using False Cons m_eq by (simp add: Let_def)
    qed
  qed
qed

end
