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

(* ---------- Target roundtrip lemma (Phase A.1 main goal) ---------- *)
(*
  The decoder inverts the encoder for every in-range n, leaving `rest`
  untouched. This is the key lemma downstream theorems cite.

  Proof sketch (port from Lean):
    1. Show varint_decode_loop on `set_cont_bits (map of_nat (to_base128 n))
       @ rest` accumulates exactly n, with the continuation bits consumed by
       the recursive case and the final 0x80-clear byte triggering the
       success branch.
    2. The n = 0 case hits the single-byte [0x00] sub-definition directly.
*)
lemma varint_decode_encode:
  assumes "n < 2 ^ 32"
  shows "varint_decode (varint_encode n @ rest) = Some (n, rest)"
  sorry

end
