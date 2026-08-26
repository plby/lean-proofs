/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.Selberg
import ErdosProblems.Erdos696.AnalyticDefinitions

namespace Erdos696

-- === Inlined from BrunTitchmarshAP ===
/-
# Brun–Titchmarsh inequality (AP form) for Erdős problem 696

Discharges `brun_titchmarsh` in `Erdos696.lean`.
Strategy: lean-pool's `SelbergSieve4` interval form + restricted Mertens
+ Solymosi-style choice of sieve level. See `PLAN-brun-titchmarsh.md`.
-/

namespace Erdos696BT

open scoped BigOperators Topology ArithmeticFunction.omega
open Filter Real Nat

/-! ## AP sieve setup -/

open scoped ArithmeticFunction.zeta

/-- The product of primes ≤ N that do not divide q. -/
noncomputable def primorialRestricted (q N : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q), p

lemma primorialRestricted_squarefree (q N : ℕ) : Squarefree (primorialRestricted q N) := by
  unfold primorialRestricted
  apply PrimeUpperBound.prodDistinctPrimes_squarefree
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hp.2.1

/-- Number of primes in `[a₀, b]` in residue class `a (mod q)`. -/
noncomputable def primesBetween_AP (a₀ b : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.Icc (Nat.ceil a₀) (Nat.floor b)).filter
    (fun n => n.Prime ∧ n % q = a % q)).card

/-- Sieve restricted to integers in `(x, x+y]` lying in `a (mod q)`. -/
noncomputable def primeInterSieveAP
    (x y z : ℝ) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) : LPSelbergSieve where
  support := (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (fun n => n % q = a % q)
  prodPrimes := primorialRestricted q (Nat.floor z)
  prodPrimes_squarefree := primorialRestricted_squarefree q _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y / q
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := z
  one_le_level := hz

/-! ## AP cardinality lemmas (CRT) -/

/-- For `d` coprime to `q`, the joint condition "d ∣ x" and "x ≡ a (mod q)" reduces
to "x ≡ k (mod dq)" where `k = chineseRemainder hdq 0 a`. -/
private lemma joint_iff_crt {d q a : ℕ} (hd : d ≠ 0) (hq : 1 ≤ q) (hdq : Nat.Coprime d q) :
    ∀ x : ℕ,
      (d ∣ x ∧ x ≡ a [MOD q]) ↔
      x ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)] := by
  intro x
  set k : ℕ := (Nat.chineseRemainder hdq 0 a : ℕ) with hk_def
  have hk_props : k ≡ 0 [MOD d] ∧ k ≡ a [MOD q] := (Nat.chineseRemainder hdq 0 a).property
  constructor
  · rintro ⟨hdx, hxq⟩
    -- x ≡ 0 (mod d) and x ≡ a (mod q); k satisfies the same. So x ≡ k mod both.
    have hxd : x ≡ k [MOD d] := by
      have h1 : x ≡ 0 [MOD d] := (Nat.modEq_zero_iff_dvd).mpr hdx
      exact h1.trans hk_props.1.symm
    have hxq' : x ≡ k [MOD q] := hxq.trans hk_props.2.symm
    exact (Nat.modEq_and_modEq_iff_modEq_mul hdq).mp ⟨hxd, hxq'⟩
  · intro hcrt
    have hxd : x ≡ k [MOD d] := hcrt.of_mul_right q
    have hxq : x ≡ k [MOD q] := hcrt.of_mul_left d
    refine ⟨?_, hxq.trans hk_props.2⟩
    exact (Nat.modEq_zero_iff_dvd).mp (hxd.trans hk_props.1)

/-- multSum for the AP sieve at a divisor `d` coprime to `q`, expressed as a count. -/
theorem multSum_AP_eq (x y z : ℝ) (hx : 0 < x) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z)
    {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    (primeInterSieveAP x y z q a hq hz).multSum d =
      ↑(((Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
        (fun n => n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])).card) := by
  unfold LPSieve.multSum
  simp only [primeInterSieveAP, Finset.sum_boole]
  -- Goal: (filter (d ∣ ·) ((Icc ⌈x⌉ ⌊x+y⌋).filter (· % q = a % q))).card = ...
  rw [Nat.cast_inj]
  -- Reduce Icc to Ioc (⌈x⌉-1)
  rw [show ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun n => n % q = a % q)).filter (fun n => d ∣ n) =
      (Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
      (fun n => d ∣ n ∧ n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])
    from ?_]
  · -- Now strip the `d ∣ n` part using joint_iff_crt
    congr 1
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨hdx, hcrt⟩; exact hcrt
    · intro hcrt
      have : d ∣ x ∧ x ≡ a [MOD q] := (joint_iff_crt hd hq hdq x).mpr hcrt
      exact ⟨this.1, hcrt⟩
  · -- The set equality
    have h_icc_ioc : Finset.Icc (Nat.ceil x) (Nat.floor (x+y)) =
        Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) := by
      rw [← Finset.Icc_succ_left_eq_Ioc]
      congr
      simpa [Nat.pred_eq_sub_one] using
        (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr hx)).symm
    rw [h_icc_ioc]
    -- Combine the two filters into one
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have hiff : (d ∣ n ∧ n % q = a % q) ↔
        (d ∣ n ∧ n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)]) := by
      constructor
      · rintro ⟨hdn, hnq⟩
        have : n ≡ a [MOD q] := hnq
        exact ⟨hdn, (joint_iff_crt hd hq hdq n).mp ⟨hdn, this⟩⟩
      · rintro ⟨hdn, hcrt⟩
        have : d ∣ n ∧ n ≡ a [MOD q] := (joint_iff_crt hd hq hdq n).mpr hcrt
        exact ⟨hdn, this.2⟩
    tauto

/-- The remainder term for the AP sieve at coprime `d`. -/
theorem rem_AP_eq (x y z : ℝ) (hx : 0 < x) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z)
    {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    (primeInterSieveAP x y z q a hq hz).rem d =
      ↑(((Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
        (fun n => n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])).card)
      - (↑d)⁻¹ * (y / (q : ℝ)) := by
  unfold LPSieve.rem
  rw [multSum_AP_eq x y z hx q a hq hz hd hdq]
  simp [primeInterSieveAP, if_neg hd]

/-- `|⌊r⌋ - r| ≤ 1` for real `r`. -/
private lemma abs_floor_sub_le (r : ℝ) : |((⌊r⌋ : ℤ) : ℝ) - r| ≤ 1 := by
  have h1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le r
  have h2 : r < ⌊r⌋ + 1 := Int.lt_floor_add_one r
  rw [abs_le]
  constructor <;> linarith

/-- Pushing `Int.floor` through `ℚ → ℝ` cast. -/
private lemma floor_rat_cast_eq_floor_real (r : ℚ) :
    ((⌊r⌋ : ℤ) : ℝ) = ((⌊(r : ℝ)⌋ : ℤ) : ℝ) := by
  congr 1; exact (Rat.floor_cast r).symm

/-- The count of integers ≡ v mod m in `Ioc a b` is within 2 of `(b - a) / m`,
provided `a ≤ b`. -/
private lemma abs_count_modEq_sub_le (a b m v : ℕ) (hm : 0 < m) (hab : a ≤ b) :
    |(((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℝ)
        - ((b : ℝ) - a) / m| ≤ 2 := by
  have hcount : (((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℤ) =
      max (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋) 0 :=
    Nat.Ioc_filter_modEq_card a b hm v
  have hm_R : (0 : ℝ) < m := by exact_mod_cast hm
  have h_q_to_R_b : ((⌊((b : ℚ) - v) / m⌋ : ℤ) : ℝ) =
      ((⌊((b : ℝ) - v) / m⌋ : ℤ) : ℝ) := by
    rw [floor_rat_cast_eq_floor_real]; congr 2; push_cast; ring
  have h_q_to_R_a : ((⌊((a : ℚ) - v) / m⌋ : ℤ) : ℝ) =
      ((⌊((a : ℝ) - v) / m⌋ : ℤ) : ℝ) := by
    rw [floor_rat_cast_eq_floor_real]; congr 2; push_cast; ring
  have hN_eq : (((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℝ) =
      ((max (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋) 0 : ℤ) : ℝ) := by
    exact_mod_cast hcount
  rw [hN_eq]
  set FbR : ℝ := ((⌊((b : ℝ) - v) / m⌋ : ℤ) : ℝ) with hFbR_def
  set FaR : ℝ := ((⌊((a : ℝ) - v) / m⌋ : ℤ) : ℝ) with hFaR_def
  have hb_close : |FbR - (((b : ℝ) - v) / m)| ≤ 1 := abs_floor_sub_le _
  have ha_close : |FaR - (((a : ℝ) - v) / m)| ≤ 1 := abs_floor_sub_le _
  have h_FF_close : |(FbR - FaR) - (((b : ℝ) - a) / m)| ≤ 2 := by
    have heq : (FbR - FaR) - (((b : ℝ) - a) / m) =
        (FbR - ((b : ℝ) - v) / m) - (FaR - ((a : ℝ) - v) / m) := by field_simp; ring
    rw [heq]
    calc |(FbR - (((b : ℝ) - v) / m)) - (FaR - (((a : ℝ) - v) / m))|
        ≤ |FbR - (((b : ℝ) - v) / m)| + |FaR - (((a : ℝ) - v) / m)| := abs_sub _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  by_cases h : (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋ : ℤ) ≤ 0
  · rw [max_eq_right h]
    push_cast
    have h_floor_le : FbR ≤ FaR := by
      have hZ : (⌊((b : ℚ) - v) / m⌋ : ℤ) ≤ ⌊((a : ℚ) - v) / m⌋ := by linarith
      have hZ_R : ((⌊((b : ℚ) - v) / m⌋ : ℤ) : ℝ) ≤ ((⌊((a : ℚ) - v) / m⌋ : ℤ) : ℝ) := by
        exact_mod_cast hZ
      rw [h_q_to_R_b, h_q_to_R_a] at hZ_R; exact hZ_R
    have hbv : (((b : ℝ) - v) / m) ≤ FbR + 1 := by rw [abs_le] at hb_close; linarith
    have hav : FaR ≤ (((a : ℝ) - v) / m) + 1 := by rw [abs_le] at ha_close; linarith
    have hba_le : ((b : ℝ) - a) / m ≤ 2 := by
      have : (((b : ℝ) - v) / m) - (((a : ℝ) - v) / m) = ((b : ℝ) - a) / m := by
        field_simp; ring
      linarith
    have hba_nn : 0 ≤ ((b : ℝ) - a) / m := by
      apply div_nonneg
      · have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
      · linarith
    rw [abs_le]; constructor <;> linarith
  · push_neg at h
    rw [max_eq_left h.le]
    push_cast
    rw [h_q_to_R_b, h_q_to_R_a]
    show |FbR - FaR - ((b : ℝ) - a) / m| ≤ 2
    exact h_FF_close

/-- Bound the AP remainder by a fixed constant `5 = 2 + 3`. -/
theorem abs_rem_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ) (hq : 1 ≤ q)
    (hz : 1 ≤ z) {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    |(primeInterSieveAP x y z q a hq hz).rem d| ≤ 5 := by
  rw [rem_AP_eq x y z hx q a hq hz hd hdq]
  set b : ℕ := Nat.floor (x + y) with hb_def
  set a' : ℕ := Nat.ceil x - 1 with ha_def
  set k : ℕ := (Nat.chineseRemainder hdq 0 a : ℕ) with hk_def
  set m : ℕ := d * q with hm_def
  have hm_pos : 0 < m := Nat.mul_pos (Nat.pos_of_ne_zero hd) hq
  have hd_R : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq
  have hm_R : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hab : a' ≤ b := by
    rw [ha_def, hb_def]
    have h_ceil_le : Nat.ceil x ≤ Nat.floor x + 1 := Nat.ceil_le_floor_add_one x
    have h_floor_le : Nat.floor x ≤ Nat.floor (x + y) := Nat.floor_mono (by linarith)
    omega
  have h_step1 := abs_count_modEq_sub_le a' b m k hm_pos hab
  set N : ℝ := (((Finset.Ioc a' b).filter (fun n => n ≡ k [MOD m])).card : ℝ) with hN_def
  have h_bx : |((b : ℝ) - (x + y))| ≤ 1 := by
    have h1 : (Nat.floor (x + y) : ℝ) ≤ x + y := Nat.floor_le (by linarith)
    have h2 : x + y < (Nat.floor (x + y) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hb_def]; rw [abs_le]; constructor <;> linarith
  have ha'_eq : (a' : ℝ) + 1 = (Nat.ceil x : ℝ) := by
    have h_ceil_ge_1 : 1 ≤ Nat.ceil x := Nat.ceil_pos.mpr hx
    rw [ha_def]
    push_cast [Nat.cast_sub h_ceil_ge_1]
    ring
  have h_ceil : |((Nat.ceil x : ℝ) - x)| ≤ 1 := by
    have h1 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_of_lt hx)
    rw [abs_le]; constructor <;> linarith
  have h_step2 : |((b : ℝ) - a') / m - y / m| ≤ 3 := by
    have h_num : |((b : ℝ) - a') - y| ≤ 3 := by
      have heq : (b : ℝ) - a' - y = ((b : ℝ) - (x + y)) - ((a' : ℝ) + 1 - x) + 1 := by ring
      rw [heq, ha'_eq]
      have h_abs_one : |(1 : ℝ)| = 1 := abs_one
      have h_sub_abs := abs_sub ((b : ℝ) - (x + y)) ((Nat.ceil x : ℝ) - x)
      calc |((b : ℝ) - (x + y)) - ((Nat.ceil x : ℝ) - x) + 1|
          ≤ |((b : ℝ) - (x + y)) - ((Nat.ceil x : ℝ) - x)| + |(1 : ℝ)| := abs_add_le _ _
        _ ≤ (|((b : ℝ) - (x + y))| + |((Nat.ceil x : ℝ) - x)|) + 1 := by linarith
        _ ≤ (1 + 1) + 1 := by linarith
        _ = 3 := by norm_num
    have hdiv : (((b : ℝ) - a') / m - y / m) = ((b : ℝ) - a' - y) / m := by rw [← sub_div]
    rw [hdiv, abs_div, abs_of_pos hm_R]
    have hm_ge_1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
    calc |((b : ℝ) - a' - y)| / m ≤ 3 / m := by gcongr
      _ ≤ 3 := by rw [div_le_iff₀ hm_R]; linarith
  have hyqm : ((d : ℝ))⁻¹ * (y / q) = y / m := by
    rw [hm_def]; push_cast; field_simp
  rw [hyqm]
  show |N - y / m| ≤ 5
  calc |N - y / m|
      = |(N - ((b : ℝ) - a') / m) + (((b : ℝ) - a') / m - y / m)| := by congr 1; ring
    _ ≤ |N - ((b : ℝ) - a') / m| + |((b : ℝ) - a') / m - y / m| := abs_add_le _ _
    _ ≤ 2 + 3 := by linarith
    _ = 5 := by norm_num

/-- Every divisor of `primorialRestricted q N` is coprime to `q`. -/
private lemma coprime_of_dvd_primorialRestricted (q N : ℕ) {d : ℕ} (hd_pos : 0 < d)
    (hd : d ∣ primorialRestricted q N) : Nat.Coprime d q := by
  rw [Nat.Coprime]
  by_contra h_ne
  have h_gcd_pos : 1 < Nat.gcd d q := by
    have h_gcd_ne_zero : Nat.gcd d q ≠ 0 := by
      intro h
      rw [Nat.gcd_eq_zero_iff] at h
      omega
    omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd d q ≠ 1)
  have hpd : p ∣ d := hp_dvd.trans (Nat.gcd_dvd_left d q)
  have hpq : p ∣ q := hp_dvd.trans (Nat.gcd_dvd_right d q)
  have hp_in_prim : p ∣ primorialRestricted q N := hpd.trans hd
  unfold primorialRestricted at hp_in_prim
  obtain ⟨p', hp'_mem, hp_dvd_p'⟩ :=
    Prime.exists_mem_finset_dvd hp_prime.prime hp_in_prim
  rw [Finset.mem_filter] at hp'_mem
  have ⟨_, hp'_prime, hp'_ndvd⟩ := hp'_mem
  have hp_eq_p' : p = p' :=
    (Nat.prime_dvd_prime_iff_eq hp_prime hp'_prime).mp hp_dvd_p'
  rw [hp_eq_p'] at hpq
  exact hp'_ndvd hpq

/-- Variant of lean-pool's `rem_sum_le_of_const` where the bound only needs to hold
for divisors of `prodPrimes`. -/
private theorem rem_sum_le_of_const_dvd (s : LPSelbergSieve) (C : ℝ) (hC : 0 ≤ C)
    (hrem : ∀ d, 0 < d → d ∣ s.prodPrimes → |s.rem d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0)
      ≤ C * s.level * (1 + Real.log s.level) ^ 3 := by
  rw [← Finset.sum_filter]
  trans (∑ d ∈ Finset.filter (fun d : ℕ => ↑d ≤ s.level)
      (s.toLPSieve.prodPrimes.divisors), (3 : ℝ) ^ ω d * C)
  · apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_ne_zero
    have h_bound : |s.rem d| ≤ C := hrem d hd_pos hd.1.1
    have h_pow_nn : (0 : ℝ) ≤ (3 : ℝ) ^ ω d := pow_nonneg (by norm_num) _
    have h_abs_nn : (0 : ℝ) ≤ |s.rem d| := abs_nonneg _
    nlinarith
  rw [show C * s.level * (1 + Real.log s.level)^3 =
      C * (s.level * (1 + Real.log s.level)^3) from by ring]
  simp_rw [show ∀ i, (3 : ℝ) ^ ω i * C = C * (3 : ℝ) ^ ω i from fun i => by ring]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC
  rw [Finset.sum_filter]
  have := Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (P := s.prodPrimes) (h := 3)
    s.level s.one_le_level s.prodPrimes_squarefree
  push_cast at this
  convert this using 2

/-- Sum of `3^ω(d) · |rem(d)|` over divisors of prodPrimes ≤ z bounded by `5z(1+log z)^3`. -/
theorem primeSieve_rem_sum_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) :
    ∑ d ∈ (primeInterSieveAP x y z q a hq hz).prodPrimes.divisors,
      (if (d : ℝ) ≤ (primeInterSieveAP x y z q a hq hz).level then
        (3 : ℝ) ^ ω d * |(primeInterSieveAP x y z q a hq hz).rem d| else 0)
      ≤ 5 * z * (1 + Real.log z) ^ 3 := by
  apply rem_sum_le_of_const_dvd (primeInterSieveAP x y z q a hq hz) 5 (by norm_num)
  intro d hd_pos hd_dvd
  have hd_coprime : Nat.Coprime d q :=
    coprime_of_dvd_primorialRestricted q (Nat.floor z) hd_pos hd_dvd
  exact abs_rem_AP_le x y z hx hy q a hq hz hd_pos.ne' hd_coprime

/-! ## Lower bound on Selberg bounding sum (AP form)

We prove `selbergBoundingSum ≥ log(z) · φ(q) / (4q)` under the strong hypothesis
`16 q^4 ≤ z`. Strategy:
1. Lower-bound `selbergBoundingSum` by `∑_{m ∈ [1, ⌊√z⌋], gcd(m,q)=1} 1/m` (adapting
   the `selbergBoundingSum_ge_sum_div` proof from lean-pool).
2. Bound the coprime harmonic sum by a block-counting argument:
   `∑_{m ≤ Mq, gcd(m,q)=1} 1/m ≥ (φ(q)/q) · log(M+1)`.
3. Choose `M = ⌊⌊√z⌋/q⌋`. With `16q^4 ≤ z`, get `M+1 ≥ 3 z^{1/4}/2 ≥ z^{1/4}`,
   so `log(M+1) ≥ log(z)/4`.
-/

/-- Helper: the radical of `m` (coprime to `q`, bounded by `z`) divides
`primorialRestricted q ⌊z⌋`. -/
private lemma rad_dvd_primorialRestricted
    (q : ℕ) (z : ℝ) (hz : 1 ≤ z) {m : ℕ} (hm_pos : 0 < m) (hm_le : (m : ℝ) ≤ z)
    (hmq : Nat.Coprime m q) :
    (∏ p ∈ m.primeFactors, p) ∣ primorialRestricted q (Nat.floor z) := by
  unfold primorialRestricted
  apply Finset.prod_dvd_prod_of_subset
  intro p hp_in
  rw [Nat.mem_primeFactors] at hp_in
  obtain ⟨hp_prime, hp_dvd, _⟩ := hp_in
  have hp_le_m : p ≤ m := Nat.le_of_dvd hm_pos hp_dvd
  have hp_le_z : (p : ℝ) ≤ z := by
    calc (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast hp_le_m
      _ ≤ z := hm_le
  have hp_le_floor : p ≤ Nat.floor z := Nat.le_floor hp_le_z
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hpq
    have hdvd_gcd : p ∣ Nat.gcd m q := Nat.dvd_gcd hp_dvd hpq
    rw [Nat.Coprime] at hmq
    rw [hmq] at hdvd_gcd
    exact hp_prime.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd_gcd)
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp_prime, hp_not_dvd_q⟩

/-- Lower bound for the AP-sieve Selberg bounding sum by the coprime harmonic sum.
This is the AP-analogue of `boundingSum_ge_sum`, adapted from `selbergBoundingSum_ge_sum_div`
in lean-pool. The key change is that we restrict the inner sum to `m` coprime to `q`. -/
private lemma selbergBoundingSum_AP_ge_coprime_sum (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    ((primeInterSieveAP x y z q a hq hz).selbergBoundingSum : ℝ) ≥
      ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
        (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ) := by
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have hnu_cm : PrimeUpperBound.CompletelyMultiplicative s.nu :=
    PrimeUpperBound.CompletelyMultiplicative.zeta.pdiv PrimeUpperBound.CompletelyMultiplicative.id
  have hnu_nonneg : ∀ n, 0 ≤ s.nu n := by
    intro n
    show 0 ≤ ((ζ : ArithmeticFunction ℝ).pdiv .id) n
    by_cases h : n = 0
    · simp [h]
    · apply div_nonneg
      · simp [h]
      · simp
  have hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1 := s.nu_lt_one_of_prime
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt z := Real.sqrt_nonneg z
  -- Chain of inequalities mirroring lean-pool's selbergBoundingSum_ge_sum_div.
  show s.selbergBoundingSum ≥ _
  dsimp only [LPSelbergSieve.selbergBoundingSum]
  calc ∑ l ∈ s.prodPrimes.divisors,
          (if ((l ^ 2 : ℕ) : ℝ) ≤ s.level then s.selbergTerms l else 0)
      ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => ((l ^ 2 : ℕ) : ℝ) ≤ s.level),
          ∑ m ∈ (l ^ Nat.floor s.level).divisors.filter (l ∣ ·), s.nu m := ?_
    _ ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt s.level))).filter
            (fun m => Nat.Coprime m q), s.nu m := ?_
    _ = ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
            (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ) := ?_
  · -- First leg: identical to the lean-pool proof.
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p ^ n))
    · rw [PrimeUpperBound.prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu_cm
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]; exact s.one_le_level
    · rw [s.selbergTerms_apply l]
      apply PrimeUpperBound.prod_factors_one_div_compMult_ge _ _ hnu_cm _ _ hlsq
      · intro p hpp hpl; exact hnu_lt p hpp (Trans.trans hpl hl.1.1)
      · exact hnu_nonneg
  · -- Second leg: show the bi-union over l's contains every coprime m ≤ √z.
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨⟨hm1, hm_le⟩, hmq⟩ := hm
        have hm_pos : 0 < m := hm1
        have hm_ne_zero : m ≠ 0 := hm_pos.ne'
        have hm_le_R : (m : ℝ) ≤ Real.sqrt s.level := by
          calc (m : ℝ) ≤ (Nat.floor (Real.sqrt s.level) : ℝ) := by exact_mod_cast hm_le
            _ ≤ Real.sqrt s.level := Nat.floor_le hsqrt_nn
        have hm_le_z : (m : ℝ) ≤ s.level := by
          calc (m : ℝ) ≤ Real.sqrt s.level := hm_le_R
            _ ≤ s.level := PrimeUpperBound.sqrt_le_self s.level s.one_le_level
        have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) :=
          Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
        have hprod_ne_zero : (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 :=
          pow_ne_zero _ hprod_pos.ne'
        rw [Finset.mem_biUnion]
        simp_rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨∏ p ∈ m.primeFactors, p, ?_, ?_⟩
        · refine ⟨⟨?_, s.prodPrimes_ne_zero⟩, ?_⟩
          · change (∏ p ∈ m.primeFactors, p) ∣ primorialRestricted q (Nat.floor z)
            exact rad_dvd_primorialRestricted q z hz hm_pos hm_le_z hmq
          · rw [← Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]),
                Nat.cast_pow, Real.sqrt_sq]
            · trans (m : ℝ)
              · norm_cast
                exact Nat.le_of_dvd hm_pos (Nat.prod_primeFactors_dvd m)
              · exact hm_le_R
            · norm_cast; omega
        · refine ⟨⟨?_, hprod_ne_zero⟩, Nat.prod_primeFactors_dvd m⟩
          rw [← Nat.factorization_le_iff_dvd hm_ne_zero hprod_ne_zero, Nat.factorization_pow]
          intro p
          have hy_mul_prod_nonneg :
              0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p :=
            Nat.zero_le _
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          trans ⌊s.level⌋₊ * Nat.factorization (∏ p ∈ m.primeFactors, p) p
          swap
          · apply le_rfl
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]
            exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]
            exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · exact le_of_lt <| Nat.factorization_lt p hm_ne_zero
            apply Nat.le_floor
            calc (m : ℝ) ≤ Real.sqrt s.level := hm_le_R
              _ ≤ s.level := PrimeUpperBound.sqrt_le_self s.level s.one_le_level
          · rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp hprod_pos.ne', pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
      · intro i _ _; apply hnu_nonneg
    · intro i hi j hj hij t hti htj n hn
      exfalso
      specialize hti hn
      specialize htj hn
      simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
      have hh : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ n → n ∣ j ^ ⌊s.level⌋₊ → i ∣ j := by
        intro i j n hiP hin hij
        apply PrimeUpperBound.nat_squarefree_dvd_pow i j _ (s.squarefree_of_dvd_prodPrimes hiP)
        exact Trans.trans hin hij
      have hidvdj : i ∣ j := hh i j hi.1.1 hti.2 htj.1.1
      have hjdvdi : j ∣ i := hh j i hj.1.1 htj.2 hti.1.1
      exact hij <| Nat.dvd_antisymm hidvdj hjdvdi
  · -- Final equality: ν(m) = 1/m for m ≥ 1, and s.level = z.
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm_ne : m ≠ 0 := by omega
    show ((ζ : ArithmeticFunction ℝ).pdiv .id) m = 1 / (m : ℝ)
    simp [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hm_ne, ArithmeticFunction.id_apply, one_div]

/-- For `q ≥ 1`, the number of integers in `(k·q, (k+1)·q]` coprime to `q` equals `φ(q)`. -/
private lemma card_block_coprime (q : ℕ) (hq : 1 ≤ q) (k : ℕ) :
    ((Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q)).card
      = q.totient := by
  classical
  have hq_pos : 0 < q := hq
  -- Step 1: shift bijection — block of size q starting at k·q matches Ioc 0 q.
  have h_shift_card :
      ((Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q)).card =
      ((Finset.Ioc 0 q).filter (fun m => Nat.Coprime m q)).card := by
    apply Finset.card_bij (fun m _ => m - k * q)
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hm
      obtain ⟨⟨h1, h2⟩, hmq⟩ := hm
      have hexp : (k + 1) * q = k * q + q := by ring
      rw [hexp] at h2
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have heq : m = (m - k * q) + k * q := by omega
      rw [Nat.Coprime, heq, Nat.gcd_add_mul_right_left] at hmq
      exact hmq
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_Ioc] at ha hb
      have hexp : (k + 1) * q = k * q + q := by ring
      rw [hexp] at ha hb
      omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h1, h2⟩, hnq⟩ := hn
      refine ⟨n + k * q, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have hexp : (k + 1) * q = k * q + q := by ring
        omega
      · rw [Nat.Coprime, Nat.gcd_add_mul_right_left]
        exact hnq
  rw [h_shift_card]
  -- Step 2: |{m ∈ Ioc 0 q : Coprime m q}| = φ(q).
  rw [Nat.totient_eq_card_coprime]
  -- target: #{m ∈ Ioc 0 q | m.Coprime q} = #{a ∈ range q | q.Coprime a}
  -- bijection: identity (within the range), using Coprime symmetric.
  by_cases hq1 : q = 1
  · subst hq1
    -- Both sides have card 1.
    have h_left : (Finset.Ioc 0 1).filter (fun m => Nat.Coprime m 1) = {1} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; omega
      · rintro rfl; exact ⟨⟨one_pos, le_refl _⟩, Nat.coprime_one_right _⟩
    have h_right : (Finset.range 1).filter (fun a => Nat.Coprime 1 a) = {0} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, _⟩; omega
      · rintro rfl; exact ⟨one_pos, Nat.coprime_one_left _⟩
    rw [h_left, h_right]
    simp
  · have hq2 : 2 ≤ q := by omega
    have h_q_not_co : ¬ Nat.Coprime q q := by
      rw [Nat.Coprime, Nat.gcd_self]; omega
    have h_0_not_co : ¬ Nat.Coprime 0 q := by
      rw [Nat.Coprime, Nat.gcd_zero_left]; omega
    have h_0_not_co' : ¬ Nat.Coprime q 0 := by
      rw [Nat.Coprime, Nat.gcd_zero_right]; omega
    -- Show both filtered sets equal {a ∈ Ico 1 q : Coprime a q}.
    have hA : (Finset.Ioc 0 q).filter (fun m => Nat.Coprime m q) =
              (Finset.Ico 1 q).filter (fun m => Nat.Coprime m q) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, hmq⟩
        refine ⟨⟨h1, ?_⟩, hmq⟩
        by_contra hc; push_neg at hc
        have : m = q := by omega
        rw [this] at hmq; exact h_q_not_co hmq
      · rintro ⟨⟨h1, h2⟩, hmq⟩; exact ⟨⟨h1, by omega⟩, hmq⟩
    have hB : (Finset.range q).filter (fun a => Nat.Coprime q a) =
              (Finset.Ico 1 q).filter (fun m => Nat.Coprime m q) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hm, hmq⟩
        refine ⟨⟨?_, hm⟩, Nat.coprime_comm.mp hmq⟩
        by_contra hc; push_neg at hc
        have : m = 0 := by omega
        rw [this] at hmq; exact h_0_not_co' hmq
      · rintro ⟨⟨h1, h2⟩, hmq⟩
        exact ⟨h2, Nat.coprime_comm.mp hmq⟩
    rw [hA, hB]

/-- Coprime harmonic block bound:
`∑_{m ≤ M·q, gcd(m,q)=1} 1/m ≥ (φ(q)/q) · ∑_{k=1}^M 1/k`. -/
private lemma coprime_harmonic_block_lower_bound (q : ℕ) (hq : 1 ≤ q) (M : ℕ) :
    ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
      ≥ (q.totient : ℝ) / q * ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := by
  classical
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  -- Partition Ioc 0 (Mq) into blocks ((k-1)q, kq] for k = 1..M (when M ≥ 1).
  -- We use the disjoint union: Ioc 0 (Mq) = ⋃_{k=0}^{M-1} Ioc (k·q) ((k+1)·q).
  -- Then sum over each block contributes ≥ φ(q)/((k+1)q).
  set blocks : ℕ → Finset ℕ := fun k =>
    (Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q) with hblocks_def
  have h_block_sum :
      (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q) =
        (Finset.range M).biUnion blocks := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_biUnion, Finset.mem_range,
      hblocks_def]
    constructor
    · rintro ⟨⟨h1, h2⟩, hmq⟩
      refine ⟨(m - 1) / q, ?_, ?_⟩
      · -- (m-1)/q < M, since m ≤ Mq so m-1 < Mq, so (m-1)/q < M.
        rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
      · refine ⟨⟨?_, ?_⟩, hmq⟩
        · -- (m-1)/q * q < m
          have h_mod : (m - 1) % q < q := Nat.mod_lt _ hq_pos
          have h_dm := Nat.div_add_mod (m - 1) q
          have h_comm : q * ((m - 1) / q) = (m - 1) / q * q := Nat.mul_comm _ _
          omega
        · -- m ≤ ((m-1)/q + 1) * q
          have hadd : ((m - 1) / q + 1) * q = (m - 1) / q * q + q := by ring
          have hmod : (m - 1) % q < q := Nat.mod_lt _ hq_pos
          have h_dm := Nat.div_add_mod (m - 1) q
          have h_comm : q * ((m - 1) / q) = (m - 1) / q * q := Nat.mul_comm _ _
          omega
    · rintro ⟨k, hkM, ⟨⟨h_lo, h_hi⟩, hmq⟩⟩
      refine ⟨⟨?_, ?_⟩, hmq⟩
      · -- 0 < m: m > k*q ≥ 0.
        have : k * q ≥ 0 := Nat.zero_le _
        omega
      · -- m ≤ M*q
        calc m ≤ (k + 1) * q := h_hi
          _ ≤ M * q := by
            apply Nat.mul_le_mul_right
            omega
  rw [h_block_sum]
  rw [Finset.sum_biUnion]
  · -- Now: ∑_{k=0}^{M-1} ∑_{m ∈ blocks k} 1/m ≥ (φ(q)/q) ∑_{k=1}^M 1/k
    -- Re-index: k' = k+1 so k=0 ↔ k'=1.
    have h_reindex :
        ∑ k ∈ Finset.range M, ∑ m ∈ blocks k, (1 : ℝ) / (m : ℝ) =
        ∑ k ∈ Finset.Icc 1 M, ∑ m ∈ blocks (k - 1), (1 : ℝ) / (m : ℝ) := by
      apply Finset.sum_bij (fun k _ => k + 1)
      · intro k hk
        rw [Finset.mem_Icc]; rw [Finset.mem_range] at hk; omega
      · intro k _ k' _ hk; omega
      · intro k hk
        rw [Finset.mem_Icc] at hk
        refine ⟨k - 1, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
      · intro k _; simp
    rw [h_reindex]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_pos : 0 < k := hk.1
    have hk_R : (0 : ℝ) < k := by exact_mod_cast hk_pos
    have hkq_R : (0 : ℝ) < (k * q : ℕ) := by exact_mod_cast Nat.mul_pos hk_pos hq_pos
    -- block (k-1) has φ(q) elements, each m ≤ k*q, so 1/m ≥ 1/(k*q).
    have hk1 : k - 1 + 1 = k := by omega
    have h_card_block : (blocks (k - 1)).card = q.totient :=
      card_block_coprime q hq (k - 1)
    -- Each m in block (k-1) satisfies m ≤ k*q.
    have h_le_kq : ∀ m ∈ blocks (k - 1), (m : ℝ) ≤ (k * q : ℕ) := by
      intro m hm
      simp only [hblocks_def] at hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      have hbound := hm.1.2
      rw [hk1] at hbound
      exact_mod_cast hbound
    have h_pos_m : ∀ m ∈ blocks (k - 1), 0 < (m : ℝ) := by
      intro m hm
      simp only [hblocks_def] at hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      have : 0 < m := by
        have : (k - 1) * q ≥ 0 := Nat.zero_le _
        omega
      exact_mod_cast this
    -- ∑_{m ∈ blocks} 1/m ≥ ∑_{m ∈ blocks} 1/(k*q) = card * 1/(k*q) = φ(q)/(k*q).
    calc ∑ m ∈ blocks (k - 1), (1 : ℝ) / (m : ℝ)
        ≥ ∑ _ ∈ blocks (k - 1), (1 : ℝ) / ((k * q : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          have hm_pos : 0 < (m : ℝ) := h_pos_m m hm
          have hm_le := h_le_kq m hm
          apply one_div_le_one_div_of_le hm_pos hm_le
      _ = (blocks (k - 1)).card * (1 / ((k * q : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (q.totient : ℝ) * (1 / ((k * q : ℕ) : ℝ)) := by rw [h_card_block]
      _ = (q.totient : ℝ) / q * (1 / (k : ℝ)) := by
          push_cast; field_simp
  · -- Pairwise disjoint blocks
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro m hm hm'
    simp only [hblocks_def, Finset.mem_filter, Finset.mem_Ioc] at hm hm'
    -- m ∈ (i*q, (i+1)*q] and m ∈ (j*q, (j+1)*q] with i ≠ j: contradiction.
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi1q : (i + 1) * q ≤ j * q := by
        apply Nat.mul_le_mul_right; omega
      have h1 := hm.1.2
      have h2 := hm'.1.1
      omega
    · have hj1q : (j + 1) * q ≤ i * q := by
        apply Nat.mul_le_mul_right; omega
      have h1 := hm'.1.2
      have h2 := hm.1.1
      omega

/-- The main bound on the AP-sieve Selberg bounding sum.

With the hypothesis `16 q^4 ≤ z`, we have
`selbergBoundingSum ≥ (φ(q)/q) · log(z) / 4`.

The constant `1/4` is explicit. The hypothesis ensures `√z/q ≥ 4q ≥ 4` and
`z^{1/4}/q ≥ 2`, which together give enough room for the `log(z)/4` lower bound
after the elementary block-counting argument. -/
theorem boundingSum_AP_ge (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hzq : 16 * (q : ℝ)^4 ≤ z) :
    ((primeInterSieveAP x y z q a hq hz).selbergBoundingSum : ℝ) ≥
      Real.log z * (q.totient : ℝ) / (4 * q) := by
  classical
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hφ_nn : (0 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.zero_le _
  -- Step 0: hypothesis implications.
  have hq4_nn : (0 : ℝ) ≤ (q : ℝ)^4 := by positivity
  have hq4_ge_1 : (1 : ℝ) ≤ (q : ℝ)^4 := by
    apply one_le_pow₀; exact_mod_cast hq
  have hz4 : (16 : ℝ) ≤ z := by linarith
  have hz_pos : 0 < z := by linarith
  have hsqrt_z_pos : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz_pos
  have hsqrt_z_ge_4 : Real.sqrt z ≥ 4 := by
    have h1 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4^2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)
    linarith [Real.sqrt_le_sqrt hz4, h1]
  -- 4 q² ≤ √z
  have h_4q2_le_sqrtz : 4 * (q : ℝ)^2 ≤ Real.sqrt z := by
    have h_sq : (4 * (q : ℝ)^2)^2 ≤ z := by
      have heq : (4 * (q : ℝ)^2)^2 = 16 * (q : ℝ)^4 := by ring
      linarith
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4 * (q : ℝ)^2)]
    exact Real.sqrt_le_sqrt h_sq
  have h_q_le_sqrtz4 : (q : ℝ) ≤ Real.sqrt z / 4 := by
    -- From 4q² ≤ √z and q ≥ 1: q ≤ q² ≤ √z/4.
    have hq_ge_1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq2_ge_q : (q : ℝ) ≤ (q : ℝ)^2 := by nlinarith
    nlinarith
  -- Step 1: lower-bound by coprime harmonic sum.
  apply le_trans (b := ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
        (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)) ?_
    (selbergBoundingSum_AP_ge_coprime_sum x y z hx hy q a hq hz)
  -- Step 2: choose N = ⌊√z⌋, M = N / q.
  set N : ℕ := Nat.floor (Real.sqrt z) with hN_def
  have hN_R_le : (N : ℝ) ≤ Real.sqrt z := Nat.floor_le (le_of_lt hsqrt_z_pos)
  have hN_R_ge : (N : ℝ) ≥ Real.sqrt z - 1 := by
    rw [hN_def]
    linarith [Nat.lt_floor_add_one (Real.sqrt z)]
  have hN_pos : 0 < N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  set M : ℕ := N / q with hM_def
  have hMq_le_N : M * q ≤ N := Nat.div_mul_le_self N q
  -- Step 3: subset sum: Ioc 0 (M*q) ⊆ Icc 1 N.
  have h_subset_sum :
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
        ≥ ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q),
            (1 : ℝ) / (m : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm.1.1, hm.1.2.trans hMq_le_N⟩, hm.2⟩
    · intro i _ _
      positivity
  -- Step 4: apply block bound.
  have h_block := coprime_harmonic_block_lower_bound q hq M
  -- Step 5: bound H_M ≥ log(M+1) ≥ log z / 4.
  -- First show M + 1 ≥ √z/(2q) ≥ z^{1/4}/√? ... actually z^{1/4} ≥ z^{1/4}.
  have hM_R_ge : ((M : ℝ) + 1) ≥ (N : ℝ) / q := by
    -- M = N/q (nat div), so M*q ≤ N, hence (M+1)*q > N, hence M+1 > N/q.
    have h_lt : N < (M + 1) * q := by
      rw [hM_def]
      have h_mod : N % q < q := Nat.mod_lt _ hq_pos
      have h_div := Nat.div_add_mod N q
      have h_div' : N / q * q + N % q = N := by
        rw [Nat.mul_comm] at h_div; omega
      have : (N / q + 1) * q = N / q * q + q := by ring
      omega
    have h_R : ((M + 1 : ℕ) : ℝ) > (N : ℝ) / q := by
      rw [gt_iff_lt, div_lt_iff₀ hq_R]
      exact_mod_cast h_lt
    push_cast at h_R
    linarith
  have hM_R_ge' : ((M : ℝ) + 1) ≥ Real.sqrt z / (2 * q) := by
    -- N ≥ √z - 1, and √z - 1 ≥ √z / 2 (since √z ≥ 2).
    have h_N_ge_half : (N : ℝ) ≥ Real.sqrt z / 2 := by linarith
    have hNq : (N : ℝ) / q ≥ Real.sqrt z / (2 * q) := by
      rw [ge_iff_le, div_le_div_iff₀ (by linarith) hq_R]
      have : Real.sqrt z * q ≤ N * (2 * q) := by nlinarith
      linarith
    linarith
  -- Strategy: work with z^{1/4} via Real.rpow.
  have hzq4_pos : 0 < z^((1:ℝ)/4) := Real.rpow_pos_of_pos hz_pos _
  have hzq4_nn : 0 ≤ z^((1:ℝ)/4) := le_of_lt hzq4_pos
  have h_2q_le_zq : 2 * (q : ℝ) ≤ z^((1:ℝ)/4) := by
    -- From 16 q^4 ≤ z, get (2q)^4 ≤ z, hence 2q ≤ z^{1/4}.
    have h_2q4 : (2 * (q : ℝ))^4 ≤ z := by nlinarith
    have h_2q_nn : (0 : ℝ) ≤ 2 * (q : ℝ) := by positivity
    -- Use Real.rpow_le_rpow_iff_left or similar.
    have h_z_eq : z = (z^((1:ℝ)/4))^4 := by
      rw [← Real.rpow_natCast (z^((1:ℝ)/4)) 4]
      rw [← Real.rpow_mul (le_of_lt hz_pos)]
      norm_num
    rw [h_z_eq] at h_2q4
    have := pow_le_pow_iff_left₀ h_2q_nn hzq4_nn (by norm_num : 4 ≠ 0) |>.mp h_2q4
    exact this
  -- √z = z^{1/2} = (z^{1/4})^2.
  have h_sqrt_eq : Real.sqrt z = z^((1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow]
  have h_z14_sq : z^((1:ℝ)/2) = (z^((1:ℝ)/4))^2 := by
    rw [show ((1:ℝ)/2) = (1:ℝ)/4 * 2 from by norm_num,
      Real.rpow_mul (le_of_lt hz_pos)]
    rw [show ((2:ℝ)) = ((2:ℕ) : ℝ) from rfl, Real.rpow_natCast]
  have hM_R_ge_zq : ((M : ℝ) + 1) ≥ z^((1:ℝ)/4) := by
    -- M+1 ≥ √z/(2q). √z = (z^{1/4})^2. 2q ≤ z^{1/4}.
    -- So √z/(2q) ≥ (z^{1/4})^2/(z^{1/4}) = z^{1/4}.
    have h_sqrt_z : Real.sqrt z = (z^((1:ℝ)/4))^2 := by rw [h_sqrt_eq, h_z14_sq]
    have h_2q_pos : 0 < 2 * (q : ℝ) := by linarith
    calc (M : ℝ) + 1 ≥ Real.sqrt z / (2 * q) := hM_R_ge'
      _ = (z^((1:ℝ)/4))^2 / (2 * q) := by rw [h_sqrt_z]
      _ ≥ (z^((1:ℝ)/4))^2 / (z^((1:ℝ)/4)) := by
          apply div_le_div_of_nonneg_left (by positivity) h_2q_pos h_2q_le_zq
      _ = z^((1:ℝ)/4) := by
          rw [sq, mul_div_assoc, div_self hzq4_pos.ne', mul_one]
  -- H_M ≥ log(M+1) ≥ log(z^{1/4}) = log(z)/4.
  have h_HM : ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ≥ Real.log z / 4 := by
    have h_inv : ∑ d ∈ Finset.Icc 1 M, (d : ℝ)⁻¹ ≥ Real.log (M + 1 : ℕ) :=
      Aux.log_add_one_le_sum_inv M
    have h_eq : ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) =
        ∑ d ∈ Finset.Icc 1 M, (d : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _; rw [one_div]
    rw [h_eq]
    refine le_trans ?_ h_inv
    have h_log_z14 : Real.log z / 4 = Real.log (z^((1:ℝ)/4)) := by
      rw [Real.log_rpow hz_pos]; ring
    rw [h_log_z14]
    apply Real.log_le_log (by positivity)
    have : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; rfl
    rw [this]
    exact hM_R_ge_zq
  -- Conclude.
  calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
      ≥ ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q),
          (1 : ℝ) / (m : ℝ) := h_subset_sum
    _ ≥ (q.totient : ℝ) / q * ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := h_block
    _ ≥ (q.totient : ℝ) / q * (Real.log z / 4) := by
        apply mul_le_mul_of_nonneg_left h_HM
        positivity
    _ = Real.log z * (q.totient : ℝ) / (4 * q) := by ring

/-! ## Final Brun–Titchmarsh AP bounds -/

/-- The Selberg sieve bound applied to the AP sieve. -/
theorem siftedSum_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hzq : 16 * (q : ℝ)^4 ≤ z) (hz1 : 1 < z) :
    (primeInterSieveAP x y z q a hq hz).siftedSum ≤
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) +
      5 * z * (1 + Real.log z) ^ 3 := by
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have hlog_pos : 0 < Real.log z := Real.log_pos hz1
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hφ_pos : 0 < q.totient := Nat.totient_pos.mpr hq_pos
  have hφ_R : (0 : ℝ) < q.totient := by exact_mod_cast hφ_pos
  have hS_pos : 0 < s.selbergBoundingSum := s.selbergBoundingSum_pos
  have hS_ge : s.selbergBoundingSum ≥ Real.log z * (q.totient : ℝ) / (4 * q) :=
    boundingSum_AP_ge x y z hx hy q a hq hz hzq
  have hbound_pos : 0 < Real.log z * (q.totient : ℝ) / (4 * q) := by positivity
  -- selberg_bound_simple gives siftedSum ≤ totalMass / S + remSum.
  apply le_trans (LPSelbergSieve.selberg_bound_simple s)
  -- totalMass = y/q, level = z.
  have htm : s.totalMass = y / q := rfl
  have hlev : s.level = z := rfl
  rw [htm]
  -- Bound y/q / S ≤ y/q / (lower bound on S).
  have hmain_bound : (y / q) / s.selbergBoundingSum ≤
      (y / q) / (Real.log z * (q.totient : ℝ) / (4 * q)) := by
    apply div_le_div_of_nonneg_left _ hbound_pos hS_ge
    positivity
  have hmain_eq : (y / q) / (Real.log z * (q.totient : ℝ) / (4 * q)) =
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) := by
    rw [div_div_eq_mul_div]
    rw [mul_comm (Real.log z) _]
    ring
  rw [hmain_eq] at hmain_bound
  have hrem_bound := primeSieve_rem_sum_AP_le x y z hx hy q a hq hz
  -- Now combine.
  linarith [hmain_bound, hrem_bound]

open Classical in
/-- Express the AP siftedSum as the cardinality of a filtered set. -/
theorem siftedSum_AP_eq_card (x y z : ℝ) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    (primeInterSieveAP x y z q a hq hz).siftedSum =
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)).card : ℝ) := by
  classical
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have h_set_eq :
      (s.support.filter (fun d => Nat.Coprime s.prodPrimes d)) =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)) := by
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at hd
      rcases hd with ⟨hd_supp, hd_cop⟩
      have hd_supp' : d ∈ (Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q) := hd_supp
      rw [Finset.mem_filter] at hd_supp'
      refine Finset.mem_filter.mpr ⟨hd_supp'.1, hd_supp'.2, ?_⟩
      intro p hpp hpz hpq hpd
      have hp_in : p ∈ ((Finset.range (Nat.floor z + 1)).filter
          (fun p => p.Prime ∧ ¬ p ∣ q)) := by
        refine Finset.mem_filter.mpr ⟨?_, hpp, hpq⟩
        rw [Finset.mem_range]
        have : p ≤ Nat.floor z := Nat.le_floor hpz
        omega
      have hp_dvd_prod : p ∣ s.prodPrimes :=
        Finset.dvd_prod_of_mem _ hp_in
      have h_one : p ∣ 1 := by
        have hgcd : p ∣ Nat.gcd s.prodPrimes d := Nat.dvd_gcd hp_dvd_prod hpd
        rwa [hd_cop] at hgcd
      exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_one h_one)
    · intro hd
      rw [Finset.mem_filter] at hd
      rcases hd with ⟨hd_icc, hd_mod, h_pf⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · -- d ∈ support
        change d ∈ (Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q)
        exact Finset.mem_filter.mpr ⟨hd_icc, hd_mod⟩
      · -- Nat.Coprime s.prodPrimes d
        rw [Nat.Coprime]
        by_contra hne
        obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hpprod : p ∣ s.prodPrimes := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
        have hpd : p ∣ d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
        have h_prod_eq : s.prodPrimes = primorialRestricted q (Nat.floor z) := rfl
        rw [h_prod_eq] at hpprod
        unfold primorialRestricted at hpprod
        rcases (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hpp) _).mp hpprod with ⟨r, hr, hpr⟩
        rcases Finset.mem_filter.mp hr with ⟨hr_range, hr_prime, hr_nq⟩
        have hpr_eq : p = r := (Nat.prime_dvd_prime_iff_eq hpp hr_prime).mp hpr
        have hp_range_mem : p ∈ Finset.range (Nat.floor z + 1) := by
          rw [hpr_eq]; exact hr_range
        rw [Finset.mem_range] at hp_range_mem
        have hpz : (p : ℝ) ≤ z := by
          have : p ≤ Nat.floor z := by omega
          calc (p : ℝ) ≤ (Nat.floor z : ℝ) := by exact_mod_cast this
            _ ≤ z := Nat.floor_le (by linarith)
        have hp_nq : ¬ p ∣ q := by rw [hpr_eq]; exact hr_nq
        exact h_pf p hpp hpz hp_nq hpd
  -- Now unfold siftedSum and convert to filtered card.
  show s.siftedSum = _
  dsimp only [LPSieve.siftedSum]
  -- weights = 1, so siftedSum = ∑ d ∈ A, if Coprime then 1 else 0 = (A.filter Coprime).card
  have h_weights : ∀ d ∈ s.support, s.weights d = 1 := fun _ _ => rfl
  have : (∑ d ∈ s.support, if Nat.Coprime s.prodPrimes d then s.weights d else 0) =
      ((s.support.filter (fun d => Nat.Coprime s.prodPrimes d)).card : ℝ) := by
    rw [← Finset.sum_filter]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [h_weights d hd.1, Nat.cast_one]
  rw [this, h_set_eq]

/-- Number of primes in an AP `≤ siftedSum + z`. -/
theorem primesBetween_AP_le_siftedSum_add (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    (primesBetween_AP x (x + y) q a : ℝ) ≤
      (primeInterSieveAP x y z q a hq hz).siftedSum + z := by
  classical
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  rw [siftedSum_AP_eq_card x y z q a hq hz]
  -- primesBetween_AP set ⊆ sifted set ∪ Icc 1 ⌊z⌋.
  have h_subset :
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n.Prime ∧ n % q = a % q)) ⊆
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))) ∪
      (Finset.Icc 1 (Nat.floor z)) := by
    intro p hp_mem
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp_mem
    rw [Finset.mem_union]
    rcases hp_mem with ⟨hp_range, hp_prime, hp_mod⟩
    by_cases hpz : (p : ℝ) ≤ z
    · right
      refine Finset.mem_Icc.mpr ⟨hp_prime.one_le, Nat.le_floor hpz⟩
    · left
      push_neg at hpz
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp_range, hp_mod, ?_⟩
      intro p' hp'_prime hp'_le _ hp'_dvd
      rw [hp_prime.dvd_iff_eq hp'_prime.ne_one] at hp'_dvd
      rw [← hp'_dvd] at hp'_le
      linarith
  have h_card_le := Finset.card_le_card h_subset
  have h_card_union := Finset.card_union_le
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))
      (Finset.Icc 1 (Nat.floor z))
  have h_card_Icc : (Finset.Icc 1 (Nat.floor z)).card ≤ Nat.floor z := by
    rw [Nat.card_Icc]; omega
  have h_floor_le : (Nat.floor z : ℝ) ≤ z := Nat.floor_le (by linarith)
  -- Combine
  have h_chain : (primesBetween_AP x (x + y) q a : ℝ) ≤
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)).card : ℝ) +
      (Nat.floor z : ℝ) := by
    have h1 : (primesBetween_AP x (x + y) q a : ℝ) ≤
        ((((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q ∧
            ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))).card +
         (Finset.Icc 1 (Nat.floor z)).card : ℝ) := by
        unfold primesBetween_AP
        exact_mod_cast le_trans h_card_le h_card_union
    have h2 : ((Finset.Icc 1 (Nat.floor z)).card : ℝ) ≤ (Nat.floor z : ℝ) := by
      exact_mod_cast h_card_Icc
    linarith
  linarith

/-- Combined Brun–Titchmarsh AP bound: number of primes in an AP is
bounded by the sifted sum plus z. -/
theorem primesBetween_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hz1 : 1 < z) (hzq : 16 * (q : ℝ)^4 ≤ z) :
    (primesBetween_AP x (x + y) q a : ℝ) ≤
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) +
      5 * z * (1 + Real.log z) ^ 3 + z := by
  have h1 := primesBetween_AP_le_siftedSum_add x y z hx hy q a hq hz
  have h2 := siftedSum_AP_le x y z hx hy q a hq hz hzq hz1
  linarith

/-- `piMod t q a` (from `Erdos696.lean`) is bounded by our `primesBetween_AP 1 t q a`. -/
theorem piMod_le_via_primesBetween_AP (t : ℝ) (q a : ℕ) (hq : 1 ≤ q) (ht : 1 ≤ t) :
    (Erdos696.piMod t q a : ℝ) ≤ primesBetween_AP 1 t q a := by
  classical
  unfold Erdos696.piMod primesBetween_AP
  have h_ceil_one : Nat.ceil (1 : ℝ) = 1 := by simp
  rw [h_ceil_one]
  -- Show the Set equals coe of the filter Finset.
  have h_set :
      {p : ℕ | p ≤ ⌊t⌋₊ ∧ p.Prime ∧ p % q = a % q} =
      ((Finset.Icc 1 ⌊t⌋₊).filter (fun n => n.Prime ∧ n % q = a % q) : Set ℕ) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_coe, Finset.mem_Icc,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp_le, hp_prime, hp_mod⟩
      exact ⟨⟨hp_prime.one_le, hp_le⟩, hp_prime, hp_mod⟩
    · rintro ⟨⟨_, hp_le⟩, hp_prime, hp_mod⟩
      exact ⟨hp_le, hp_prime, hp_mod⟩
  rw [h_set, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- The elementary error from the sieve is absorbed at level `sqrt u`. -/
private lemma sieve_error_le {u : ℝ} (hu : 256 ≤ u) :
    5 * Real.sqrt u * (1 + Real.log (Real.sqrt u)) ^ 3 + Real.sqrt u ≤
      24576 * u / Real.log u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hlog : 2 ≤ Real.log u := by
    have h256 : (2 : ℝ) ≤ Real.log 256 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [Real.log_two_gt_d9]
    exact h256.trans (Real.log_le_log (by norm_num) hu)
  have hlog0 : 0 < Real.log u := lt_of_lt_of_le (by norm_num) hlog
  have hs0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hcube : (1 + Real.log (Real.sqrt u)) ^ 3 ≤ Real.log u ^ 3 := by
    rw [Real.log_sqrt hu0.le]
    apply pow_le_pow_left₀ (by linarith only [hlog])
    linarith only [hlog]
  have hcube1 : (1 : ℝ) ≤ Real.log u ^ 3 := one_le_pow₀ (by linarith only [hlog])
  have hp : Real.log u ^ 4 ≤ 4096 * Real.sqrt u := by
    have h := Real.log_le_rpow_div hu0.le (by norm_num : (0 : ℝ) < 1 / 8)
    have hp := pow_le_pow_left₀ hlog0.le h 4
    apply hp.trans_eq
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
    norm_num [Real.sqrt_eq_rpow]
    ring
  calc
    _ ≤ 6 * Real.sqrt u * Real.log u ^ 3 := by
      nlinarith only [mul_nonneg hs0 (sub_nonneg.mpr hcube),
        mul_nonneg hs0 (sub_nonneg.mpr hcube1)]
    _ ≤ 24576 * u / Real.log u := by
      rw [le_div_iff₀ hlog0]
      calc
        _ = 6 * Real.sqrt u * Real.log u ^ 4 := by ring
        _ ≤ 6 * Real.sqrt u * (4096 * Real.sqrt u) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = 24576 * u := by nlinarith only [Real.sq_sqrt hu0.le]

/-- Brun–Titchmarsh for the range needed by the chain construction. -/
theorem brun_titchmarsh_large :
    ∃ CBT : ℝ, 0 < CBT ∧
      ∀ q : ℕ, 1 ≤ q →
        ∀ a : ℕ, Nat.Coprime a q →
          ∀ t : ℝ, 256 * (q : ℝ)^9 ≤ t →
            (Erdos696.piMod t q a : ℝ) ≤
              CBT * t / ((q.totient : ℝ) * Real.log (t / q)) := by
  refine ⟨30000, by norm_num, ?_⟩
  intro q hq a _hcop t ht
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have ht256 : (256 : ℝ) ≤ t := by
    calc
      256 ≤ 256 * (q : ℝ) ^ 9 := by nlinarith only [one_le_pow₀ hq1 (n := 9)]
      _ ≤ t := ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht256
  let u : ℝ := t / q
  let z : ℝ := Real.sqrt u
  have hu : 256 * (q : ℝ) ^ 8 ≤ u := by
    apply (le_div_iff₀ hq0).mpr
    calc
      _ = 256 * (q : ℝ) ^ 9 := by ring
      _ ≤ t := ht
  have hu256 : 256 ≤ u := by
    calc
      256 ≤ 256 * (q : ℝ) ^ 8 := by nlinarith only [one_le_pow₀ hq1 (n := 8)]
      _ ≤ u := hu
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu256
  have hzq : 16 * (q : ℝ) ^ 4 ≤ z := by
    apply (Real.le_sqrt (by positivity) hu0.le).mpr
    calc
      _ = 256 * (q : ℝ) ^ 8 := by ring
      _ ≤ u := hu
  have hz16 : 16 ≤ z := by
    calc
      16 ≤ 16 * (q : ℝ) ^ 4 := by nlinarith only [one_le_pow₀ hq1 (n := 4)]
      _ ≤ z := hzq
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) hz16
  have hlog0 : 0 < Real.log u := Real.log_pos (by linarith only [hu256])
  have hphi0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hphiq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hd : 0 < (q.totient : ℝ) * Real.log u := mul_pos hphi0 hlog0
  have hraw := primesBetween_AP_le 1 (t - 1) z (by norm_num)
    (by linarith only [ht256]) q a hq hz1.le hz1 hzq
  rw [show (1 : ℝ) + (t - 1) = t by ring] at hraw
  have hmain :
      4 * (q : ℝ) * ((t - 1) / q) / ((q.totient : ℝ) * Real.log z) ≤
        8 * t / ((q.totient : ℝ) * Real.log u) := by
    have heq :
        4 * (q : ℝ) * ((t - 1) / q) / ((q.totient : ℝ) * Real.log z) =
          8 * (t - 1) / ((q.totient : ℝ) * Real.log u) := by
      dsimp only [z]
      rw [Real.log_sqrt hu0.le]
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ hd.le
    linarith only
  have herr : 5 * z * (1 + Real.log z)^3 + z ≤
      24576 * t / ((q.totient : ℝ) * Real.log u) := by
    apply (sieve_error_le hu256).trans
    rw [div_le_div_iff₀ hlog0 hd]
    have htu : t = (q : ℝ) * u := by dsimp [u]; field_simp
    rw [htu]
    calc
      24576 * u * ((q.totient : ℝ) * Real.log u) =
          (24576 * u * Real.log u) * q.totient := by ring
      _ ≤ (24576 * u * Real.log u) * q :=
        mul_le_mul_of_nonneg_left hphiq (by positivity)
      _ = _ := by ring
  have hpi := (piMod_le_via_primesBetween_AP t q a hq
    (by linarith only [ht256])).trans hraw
  change (piMod t q a : ℝ) ≤ 30000 * t / ((q.totient : ℝ) * Real.log u)
  have hcoeff : (8 + 24576 : ℝ) * t / ((q.totient : ℝ) * Real.log u) ≤
      30000 * t / ((q.totient : ℝ) * Real.log u) := by
    apply div_le_div_of_nonneg_right _ hd.le
    nlinarith only [ht0.le]
  have hadd : 8 * t / ((q.totient : ℝ) * Real.log u) +
      24576 * t / ((q.totient : ℝ) * Real.log u) =
        (8 + 24576 : ℝ) * t / ((q.totient : ℝ) * Real.log u) := by ring
  linarith only [hpi, hmain, herr, hcoeff, hadd]

end Erdos696BT

end Erdos696
