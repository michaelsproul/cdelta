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

(* ---------- Phase A.2 main goal: encode/decode inversion ---------- *)
(*
  For any address below the 32-bit wire limit, encode_address produces
  bytes such that decode_address with the same mode on those bytes
  recovers (addr, tail, updated-cache). The cache is threaded identically
  through both sides — essential for the inductive proof over multiple
  COPYs.
*)
lemma encode_decode_address:
  assumes "addr < 2 ^ 32" "here < 2 ^ 32"
  shows
    "let (mode, bs, c') = encode_address c addr here
     in decode_address c mode here (bs @ rest) = Some (addr, rest, c')"
  sorry

(* Mode returned by encode_address is always a valid one (< num_modes). *)
lemma encode_address_mode_bound:
  "fst (encode_address c addr here) < num_modes"
  sorry

end
