/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analytic helpers for Erdős Problem 784

This file develops the elementary Hardy--Ramanujan upper-normal-order
estimate needed for the Schinzel--Szekeres boundary construction.  It is
kept separate from `Erdos784.lean` so that the finite sieve argument can be
checked independently.
-/

open scoped BigOperators Topology ArithmeticFunction.Omega ArithmeticFunction.omega
open Filter Finset MeasureTheory

namespace Erdos784.Analytic

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Sum of the reciprocals of the primes at most `N`. -/
def primeReciprocals (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesLE, (p : ℝ)⁻¹

lemma primeReciprocals_nonneg (N : ℕ) : 0 ≤ primeReciprocals N := by
  exact sum_nonneg fun _ _ => inv_nonneg.mpr (by positivity)

lemma primeReciprocals_eq_sum_Icc (N : ℕ) :
    primeReciprocals N =
      ∑ n ∈ Icc 0 N, if n.Prime then (n : ℝ)⁻¹ else 0 := by
  rw [primeReciprocals, Nat.primesLE_eq_filter_Icc_zero, sum_filter]

lemma primeReciprocals_floor_eq_sum_Icc (x : ℝ) :
    primeReciprocals ⌊x⌋₊ =
      ∑ n ∈ Icc 0 ⌊x⌋₊, if n.Prime then (n : ℝ)⁻¹ else 0 :=
  primeReciprocals_eq_sum_Icc _

lemma integrableOn_primeCounting_div_sq (x : ℝ) :
    IntegrableOn (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2)
      (Set.Icc 2 x) volume := by
  conv => arg 1; ext t
          rw [div_eq_mul_one_div, mul_comm, Nat.primeCounting, Nat.primeCounting',
            Nat.count_eq_card_filter_range, card_eq_sum_ones, Nat.cast_sum,
            Nat.range_succ_eq_Icc_zero, sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht => ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have ht20 : t ^ 2 ≠ 0 := pow_ne_zero _ ht0
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/-- Abel summation for the prime reciprocal sum. -/
lemma primeReciprocals_eq_primeCounting_div_add_integral {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocals ⌊x⌋₊ =
      (Nat.primeCounting ⌊x⌋₊ : ℝ) / x +
        ∫ t in 2..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  rw [primeReciprocals_floor_eq_sum_Icc]
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun _ => 1)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (n : ℝ)⁻¹ * a n
  · apply sum_congr rfl
    intro n _
    split_ifs with hn
    · simp [a, hn]
    · simp [a, hn]
  rw [sum_mul_eq_sub_integral_mul₁ a (by simp [a, Nat.not_prime_zero])
    (by simp [a, Nat.not_prime_one])]
  · rw [← intervalIntegral.integral_of_le hx]
    have hDeriv (t : ℝ) : deriv (fun u : ℝ => u⁻¹) t = -(t ^ 2)⁻¹ := by
      rw [deriv_inv']
    simp only [a, Set.indicator_apply, Set.mem_ofPred]
    rw [show (∑ k ∈ Icc 0 ⌊x⌋₊, if k.Prime then (1 : ℝ) else 0) =
        Nat.primeCounting ⌊x⌋₊ by
      simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
        Nat.range_succ_eq_Icc_zero]]
    simp_rw [hDeriv]
    have hSum (t : ℝ) :
        (∑ k ∈ Icc 0 ⌊t⌋₊, if k.Prime then (1 : ℝ) else 0) =
          Nat.primeCounting ⌊t⌋₊ := by
      simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
        Nat.range_succ_eq_Icc_zero]
    simp_rw [hSum]
    ring_nf
    rw [intervalIntegral.integral_neg]
    rw [sub_neg_eq_add]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    ring
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    fun_prop

/-- Chebyshev's estimate and Abel summation give the correct leading
constant in the elementary upper bound for the prime reciprocal sum. -/
lemma primeReciprocals_le_log_log_add_const {δ : ℝ} (hδ : 0 < δ) :
    ∃ T C : ℝ, 3 ≤ T ∧ 0 ≤ C ∧ ∀ x : ℝ, T ≤ x →
      primeReciprocals ⌊x⌋₊ ≤ (Real.log 4 + δ) * Real.log (Real.log x) + C := by
  let K := Real.log 4 + δ
  have hKpos : 0 < K := add_pos (Real.log_pos (by norm_num)) hδ
  have hpi := Chebyshev.eventually_primeCounting_le hδ
  rw [eventually_atTop] at hpi
  obtain ⟨T₀, hT₀⟩ := hpi
  let T : ℝ := max T₀ (max 3 (Real.exp 1))
  let f : ℝ → ℝ := fun t => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2
  let C : ℝ := |∫ t in 2..T, f t| + K * |Real.log (Real.log T)| + K + 1
  have hT3 : 3 ≤ T := le_max_of_le_right (le_max_left _ _)
  have hTexp : Real.exp 1 ≤ T := le_max_of_le_right (le_max_right _ _)
  have hT0 : T₀ ≤ T := le_max_left _ _
  have hTlog : 1 ≤ Real.log T := by
    have hTpos : 0 < T := by linarith
    rw [Real.le_log_iff_exp_le hTpos]
    exact hTexp
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog4 : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
    positivity
  refine ⟨T, C, hT3, hC, ?_⟩
  intro x hTx
  have hx2 : 2 ≤ x := hT3.trans hTx |>.trans' (by norm_num)
  have hxT0 : T₀ ≤ x := hT0.trans hTx
  have hpiX := hT₀ x hxT0
  have hxPos : 0 < x := by linarith
  have hxLog : 1 ≤ Real.log x := hTlog.trans (Real.log_le_log (by linarith) hTx)
  have hBoundary : (Nat.primeCounting ⌊x⌋₊ : ℝ) / x ≤ K := by
    calc
      (Nat.primeCounting ⌊x⌋₊ : ℝ) / x ≤ (K * x / Real.log x) / x :=
        div_le_div_of_nonneg_right hpiX hxPos.le
      _ = K / Real.log x := by field_simp
      _ ≤ K := by
        simpa using div_le_self hKpos.le hxLog
  have hInt2T : IntervalIntegrable f volume 2 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [hT3])]
    simpa [f] using integrableOn_primeCounting_div_sq T
  have hIntTx : IntervalIntegrable f volume T x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTx]
    apply (integrableOn_primeCounting_div_sq x).mono_set
    exact Set.Icc_subset_Icc (by linarith [hT3]) (le_refl x)
  have hMajorInt :
      ∫ t in T..x, f t ≤ K * (Real.log (Real.log x) - Real.log (Real.log T)) := by
    calc
      ∫ t in T..x, f t ≤ ∫ t in T..x, K * (t⁻¹ / Real.log t) := by
        refine intervalIntegral.integral_mono_on hTx hIntTx ?_ ?_
        · refine ContinuousOn.intervalIntegrable fun t ht =>
            ContinuousAt.continuousWithinAt ?_
          rw [Set.uIcc_of_le hTx] at ht
          have ht1 : 1 < t := by linarith [hT3, ht.1]
          have ht0 : t ≠ 0 := by linarith
          have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
          fun_prop
        · intro t ht
          rw [Set.mem_Icc] at ht
          have htT0 : T₀ ≤ t := hT0.trans ht.1
          have htPos : 0 < t := by linarith [hT3, ht.1]
          have htLogPos : 0 < Real.log t := Real.log_pos (by linarith [hT3, ht.1])
          have hp := hT₀ t htT0
          dsimp [f]
          calc
            (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤ (K * t / Real.log t) / t ^ 2 :=
              div_le_div_of_nonneg_right hp (sq_nonneg t)
            _ = K * (t⁻¹ / Real.log t) := by field_simp
      _ = K * (Real.log (Real.log x) - Real.log (Real.log T)) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_div_log (by linarith) (by linarith)]
  rw [primeReciprocals_eq_primeCounting_div_add_integral hx2,
    ← intervalIntegral.integral_add_adjacent_intervals hInt2T hIntTx]
  calc
    (Nat.primeCounting ⌊x⌋₊ : ℝ) / x +
        ((∫ t in 2..T, f t) + ∫ t in T..x, f t) ≤
      K + (|∫ t in 2..T, f t| +
        K * (Real.log (Real.log x) - Real.log (Real.log T))) :=
      add_le_add hBoundary (add_le_add (le_abs_self _) hMajorInt)
    _ = K + |∫ t in 2..T, f t| +
        K * (Real.log (Real.log x) - Real.log (Real.log T)) := by ring
    _ ≤ K * Real.log (Real.log x) + C := by
      dsimp [C]
      have hneg : -K * Real.log (Real.log T) ≤ K * |Real.log (Real.log T)| := by
        simpa [neg_mul] using
          (mul_le_mul_of_nonneg_left (neg_le_abs (Real.log (Real.log T))) hKpos.le)
      linarith

lemma eventually_primeReciprocals_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      primeReciprocals ⌊x⌋₊ ≤ (Real.log 4 + ε) * Real.log (Real.log x) := by
  obtain ⟨T, C, _hT, hC, hBound⟩ :=
    primeReciprocals_le_log_log_add_const (show 0 < ε / 2 by positivity)
  have hLittle := (Real.one_isLittleO_log_log.const_mul_left C).bound
    (show 0 < ε / 2 by positivity)
  filter_upwards [eventually_ge_atTop T, hLittle,
      eventually_gt_atTop (Real.exp 1)] with x hxT hxC hx
  have hloglog : 0 ≤ Real.log (Real.log x) := by
    have hxpos : 0 < x := (Real.exp_pos 1).trans hx
    have hlog1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hx.le
    exact Real.log_nonneg hlog1
  have hC' : C ≤ ε / 2 * Real.log (Real.log x) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hC, abs_of_nonneg hloglog] using hxC
  calc
    primeReciprocals ⌊x⌋₊ ≤ (Real.log 4 + ε / 2) * Real.log (Real.log x) + C := hBound x hxT
    _ ≤ (Real.log 4 + ε) * Real.log (Real.log x) := by nlinarith

/-! ## A finite Turán estimate for `Ω` -/

/-- Prime powers `p^k ≤ Y`, retaining `(p,k)` because multiplicity matters. -/
def primePowerIndices (Y : ℕ) : Finset (ℕ × ℕ) :=
  (Y.primesLE ×ˢ Icc 1 (Nat.log 2 Y)).filter fun pk => pk.1 ^ pk.2 ≤ Y

@[simp] lemma mem_primePowerIndices {Y p k : ℕ} :
    (p, k) ∈ primePowerIndices Y ↔
      p.Prime ∧ p ≤ Y ∧ 1 ≤ k ∧ k ≤ Nat.log 2 Y ∧ p ^ k ≤ Y := by
  simp only [primePowerIndices, mem_filter, mem_product, Nat.mem_primesLE, mem_Icc]
  tauto

lemma support_factorization_subset_primesLE {Y n : ℕ} (hnPos : 0 < n) (hnY : n ≤ Y) :
    n.factorization.support ⊆ Y.primesLE := by
  intro p hp
  have hpData := Nat.mem_primeFactors.mp (Nat.support_factorization n ▸ hp)
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hnPos hpData.2.1).trans hnY, hpData.1⟩

lemma factorization_eq_sum_pow_dvd {Y n p : ℕ} (hnPos : 0 < n) (hnY : n ≤ Y)
    (hp : p ∈ Y.primesLE) :
    n.factorization p = ∑ k ∈ Icc 1 (Nat.log 2 Y), if p ^ k ∣ n then 1 else 0 := by
  have hpPrime := Nat.prime_of_mem_primesLE hp
  have hFinset :
      {k ∈ Ico 1 n | p ^ k ∣ n} =
        {k ∈ Icc 1 (Nat.log 2 Y) | p ^ k ∣ n} := by
    ext k
    simp only [mem_filter, mem_Ico, mem_Icc]
    constructor
    · rintro ⟨⟨hkPos, _hkn⟩, hdiv⟩
      have hpowN : p ^ k ≤ n := Nat.le_of_dvd hnPos hdiv
      have htwo : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hpPrime.two_le k
      exact ⟨⟨hkPos, Nat.le_log_of_pow_le Nat.one_lt_two
        (htwo.trans (hpowN.trans hnY))⟩, hdiv⟩
    · rintro ⟨⟨hkPos, _hklog⟩, hdiv⟩
      exact ⟨⟨hkPos, Nat.lt_of_pow_dvd_right hnPos.ne' hpPrime.one_lt hdiv⟩, hdiv⟩
  rw [Nat.factorization_eq_card_pow_dvd n hpPrime, hFinset, card_eq_sum_ones, sum_filter]

lemma omega_eq_sum_primePowerIndicators {Y n : ℕ} (hnPos : 0 < n) (hnY : n ≤ Y) :
    Ω n = ∑ pk ∈ primePowerIndices Y, if pk.1 ^ pk.2 ∣ n then 1 else 0 := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
  rw [Finsupp.sum_of_support_subset n.factorization
    (support_factorization_subset_primesLE hnPos hnY) (fun _ k => k) (by simp)]
  calc
    ∑ p ∈ Y.primesLE, n.factorization p =
        ∑ p ∈ Y.primesLE, ∑ k ∈ Icc 1 (Nat.log 2 Y),
          if p ^ k ∣ n then 1 else 0 := by
      apply sum_congr rfl
      intro p hp
      exact factorization_eq_sum_pow_dvd hnPos hnY hp
    _ = ∑ pk ∈ primePowerIndices Y, if pk.1 ^ pk.2 ∣ n then 1 else 0 := by
      rw [← Finset.sum_product Y.primesLE (Icc 1 (Nat.log 2 Y))
        (fun pk => if pk.1 ^ pk.2 ∣ n then 1 else 0)]
      simp only [primePowerIndices, sum_filter]
      apply sum_congr rfl
      intro pk hpk
      by_cases hpow : pk.1 ^ pk.2 ≤ Y
      · simp [hpow]
      · have hnot : ¬pk.1 ^ pk.2 ∣ n := fun hdvd =>
          hpow ((Nat.le_of_dvd hnPos hdvd).trans hnY)
        simp [hpow, hnot]

/-! It is more economical to estimate the distinct-prime count `ω` first and
then control `Ω - ω` by the convergent tail of prime powers. -/

lemma omega_eq_sum_primeIndicators {Y n : ℕ} (hnPos : 0 < n) (hnY : n ≤ Y) :
    ω n = ∑ p ∈ Y.primesLE, if p ∣ n then 1 else 0 := by
  have hcard : ω n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply,
      ← List.card_toFinset, Nat.toFinset_factors]
  calc
    ω n = n.primeFactors.card := hcard
    _ = ∑ p ∈ n.primeFactors, 1 := card_eq_sum_ones _
    _ = ∑ p ∈ Y.primesLE, if p ∣ n then 1 else 0 := by
      rw [← sum_filter]
      congr 2
      ext p
      by_cases hp : p.Prime
      · simp only [mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors, hp, and_true,
          true_and]
        constructor
        · rintro ⟨hpn, _⟩
          exact ⟨(Nat.le_of_dvd hnPos hpn).trans hnY, hpn⟩
        · rintro ⟨_, hpn⟩
          exact ⟨hpn, hnPos.ne'⟩
      · simp [Nat.mem_primeFactors, hp, Nat.mem_primesLE]

lemma sum_omega_eq_sum_div (Y : ℕ) :
    ∑ n ∈ Ioc 0 Y, ω n = ∑ p ∈ Y.primesLE, Y / p := by
  calc
    ∑ n ∈ Ioc 0 Y, ω n =
        ∑ n ∈ Ioc 0 Y, ∑ p ∈ Y.primesLE, if p ∣ n then 1 else 0 := by
      apply sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      exact omega_eq_sum_primeIndicators hn'.1 hn'.2
    _ = ∑ p ∈ Y.primesLE, ∑ n ∈ Ioc 0 Y, if p ∣ n then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ p ∈ Y.primesLE, Y / p := by
      apply sum_congr rfl
      intro p _hp
      rw [← sum_filter]
      rw [← card_eq_sum_ones]
      exact Nat.Ioc_filter_dvd_card_eq_div Y p

lemma sum_omega_sq_eq_sum_lcm_div (Y : ℕ) :
    ∑ n ∈ Ioc 0 Y, (ω n) ^ 2 =
      ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE, Y / Nat.lcm p q := by
  calc
    ∑ n ∈ Ioc 0 Y, (ω n) ^ 2 =
        ∑ n ∈ Ioc 0 Y,
          (∑ p ∈ Y.primesLE, if p ∣ n then 1 else 0) ^ 2 := by
      apply sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      rw [omega_eq_sum_primeIndicators hn'.1 hn'.2]
    _ = ∑ n ∈ Ioc 0 Y, ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE,
          (if p ∣ n then 1 else 0) * (if q ∣ n then 1 else 0) := by
      apply sum_congr rfl
      intro n _hn
      simp only [pow_two, sum_mul_sum]
    _ = ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE, ∑ n ∈ Ioc 0 Y,
          (if p ∣ n then 1 else 0) * (if q ∣ n then 1 else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _hp
      rw [sum_comm]
    _ = ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE, Y / Nat.lcm p q := by
      apply sum_congr rfl
      intro p _hp
      apply sum_congr rfl
      intro q _hq
      have hfilter : (Ioc 0 Y).filter (fun n => p ∣ n ∧ q ∣ n) =
          (Ioc 0 Y).filter (fun n => Nat.lcm p q ∣ n) := by
        ext n
        simp only [mem_filter]
        constructor
        · rintro ⟨hn, hp, hq⟩
          exact ⟨hn, Nat.lcm_dvd hp hq⟩
        · rintro ⟨hn, hlcm⟩
          exact ⟨hn, (Nat.dvd_lcm_left p q).trans hlcm,
            (Nat.dvd_lcm_right p q).trans hlcm⟩
      calc
        ∑ n ∈ Ioc 0 Y, (if p ∣ n then 1 else 0) * (if q ∣ n then 1 else 0) =
            ∑ n ∈ (Ioc 0 Y).filter (fun n => p ∣ n ∧ q ∣ n), 1 := by
          rw [sum_filter]
          apply sum_congr rfl
          intro n _hn
          by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq]
        _ = ∑ n ∈ (Ioc 0 Y).filter (fun n => Nat.lcm p q ∣ n), 1 := by rw [hfilter]
        _ = Y / Nat.lcm p q := by
          rw [← card_eq_sum_ones]
          exact Nat.Ioc_filter_dvd_card_eq_div Y (Nat.lcm p q)

lemma div_sub_one_lt_cast_natDiv {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / b - 1 < (a / b : ℕ) := by
  rw [sub_lt_iff_lt_add, (div_lt_iff₀ (Nat.cast_pos.mpr hb))]
  have hmod : ((a % b : ℕ) : ℝ) < b := by exact_mod_cast Nat.mod_lt a hb
  have hdecomp : (a : ℝ) = b * (a / b : ℕ) + ((a % b : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod a b).symm
  rw [hdecomp]
  nlinarith

lemma omega_firstMoment_lower (Y : ℕ) :
    (Y : ℝ) * primeReciprocals Y - Nat.primeCounting Y ≤
      ∑ n ∈ Ioc 0 Y, (ω n : ℝ) := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    (Y : ℝ) * primeReciprocals Y - (Y.primesLE.card : ℕ) =
        ∑ p ∈ Y.primesLE, ((Y : ℝ) / p - 1) := by
      simp only [primeReciprocals, sum_sub_distrib, sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ ∑ p ∈ Y.primesLE, ((Y / p : ℕ) : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact (div_sub_one_lt_cast_natDiv
        (Nat.prime_of_mem_primesLE hp).pos).le
    _ = ∑ n ∈ Ioc 0 Y, (ω n : ℝ) := by
      exact_mod_cast (sum_omega_eq_sum_div Y).symm

lemma omega_secondMoment_upper (Y : ℕ) :
    ∑ n ∈ Ioc 0 Y, ((ω n : ℝ) ^ 2) ≤
      (Y : ℝ) * (primeReciprocals Y ^ 2 + primeReciprocals Y) := by
  have hsecond := congrArg (fun z : ℕ => (z : ℝ)) (sum_omega_sq_eq_sum_lcm_div Y)
  simp only [Nat.cast_sum, Nat.cast_pow] at hsecond
  rw [hsecond]
  calc
    ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE,
          ((Y / Nat.lcm p q : ℕ) : ℝ) ≤
        ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE,
          ((Y : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ +
            if p = q then (Y : ℝ) * (p : ℝ)⁻¹ else 0) := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro q hq
      have hpPrime := Nat.prime_of_mem_primesLE hp
      have hqPrime := Nat.prime_of_mem_primesLE hq
      by_cases hpq : p = q
      · subst q
        rw [Nat.lcm_self]
        have hfloor : ((Y / p : ℕ) : ℝ) ≤ (Y : ℝ) / p := Nat.cast_div_le
        rw [if_pos rfl]
        have hbase : 0 ≤ (Y : ℝ) * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by positivity
        have hfloor' : ((Y / p : ℕ) : ℝ) ≤ (Y : ℝ) * (p : ℝ)⁻¹ := by
          simpa only [div_eq_mul_inv] using hfloor
        exact hfloor'.trans (le_add_of_nonneg_left hbase)
      · have hcop : p.Coprime q := (Nat.coprime_primes hpPrime hqPrime).2 hpq
        rw [hcop.lcm_eq_mul, if_neg hpq]
        simpa only [add_zero, Nat.cast_mul, div_eq_mul_inv, mul_inv, mul_assoc] using
          (Nat.cast_div_le (α := ℝ) (m := Y) (n := p * q))
    _ = (Y : ℝ) * (primeReciprocals Y ^ 2 + primeReciprocals Y) := by
      simp only [sum_add_distrib]
      have hfirst :
          ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE,
              (Y : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ =
            (Y : ℝ) * primeReciprocals Y ^ 2 := by
        rw [primeReciprocals, pow_two, ← Finset.sum_mul_sum]
        rw [← Finset.mul_sum]
        ring
      have hdiag :
          ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE,
              (if p = q then (Y : ℝ) * (p : ℝ)⁻¹ else 0) =
            (Y : ℝ) * primeReciprocals Y := by
        calc
          ∑ p ∈ Y.primesLE, ∑ q ∈ Y.primesLE,
              (if p = q then (Y : ℝ) * (p : ℝ)⁻¹ else 0) =
              ∑ p ∈ Y.primesLE, (Y : ℝ) * (p : ℝ)⁻¹ := by
            apply sum_congr rfl
            intro p hp
            simp [hp]
          _ = (Y : ℝ) * primeReciprocals Y := by
            rw [primeReciprocals, Finset.mul_sum]
      rw [hfirst, hdiag]
      ring

lemma primeCounting_le_self (Y : ℕ) : Nat.primeCounting Y ≤ Y := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    Y.primesLE.card ≤ (Ioc 0 Y).card := by
      apply card_le_card
      intro p hp
      have hp' := Nat.mem_primesLE.mp hp
      exact Finset.mem_Ioc.mpr ⟨hp'.2.pos, hp'.1⟩
    _ = Y := by simp

/-- Finite Turán inequality for the number of distinct prime factors.  The
slightly generous constant `3` lets us avoid using a prime-number estimate in
the floor-error term. -/
lemma omega_variance_upper (Y : ℕ) :
    ∑ n ∈ Ioc 0 Y, ((ω n : ℝ) - primeReciprocals Y) ^ 2 ≤
      3 * (Y : ℝ) * primeReciprocals Y := by
  let P := primeReciprocals Y
  let S₁ : ℝ := ∑ n ∈ Ioc 0 Y, (ω n : ℝ)
  let S₂ : ℝ := ∑ n ∈ Ioc 0 Y, (ω n : ℝ) ^ 2
  have hP : 0 ≤ P := primeReciprocals_nonneg Y
  have hfirst : (Y : ℝ) * P - Nat.primeCounting Y ≤ S₁ :=
    omega_firstMoment_lower Y
  have hsecond : S₂ ≤ (Y : ℝ) * (P ^ 2 + P) :=
    omega_secondMoment_upper Y
  have hpi : (Nat.primeCounting Y : ℝ) ≤ Y := by
    exact_mod_cast primeCounting_le_self Y
  have hrewrite :
      ∑ n ∈ Ioc 0 Y, ((ω n : ℝ) - P) ^ 2 =
        S₂ - S₁ * P * 2 + (Y : ℝ) * P ^ 2 := by
    dsimp only [S₁, S₂]
    simp only [sub_sq, sum_sub_distrib, sum_add_distrib, Finset.sum_mul,
      sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
    have hsumcomm :
        ∑ n ∈ Ioc 0 Y, 2 * (ω n : ℝ) * P =
          ∑ n ∈ Ioc 0 Y, P * (ω n : ℝ) * 2 := by
      apply sum_congr rfl
      intro n _hn
      ring
    rw [hsumcomm]
    apply congrArg (fun z : ℝ =>
      (∑ n ∈ Ioc 0 Y, (ω n : ℝ) ^ 2) - z + (Y : ℝ) * P ^ 2)
    apply sum_congr rfl
    intro n _hn
    ring
  change ∑ n ∈ Ioc 0 Y, ((ω n : ℝ) - P) ^ 2 ≤ 3 * (Y : ℝ) * P
  rw [hrewrite]
  have hneg : -2 * P ≤ 0 := by nlinarith
  have hmul := mul_le_mul_of_nonpos_left hfirst hneg
  nlinarith

def higherPrimePowerIndices (Y : ℕ) : Finset (ℕ × ℕ) :=
  (primePowerIndices Y).filter fun pk => 2 ≤ pk.2

def firstPrimePowerIndices (Y : ℕ) : Finset (ℕ × ℕ) :=
  (primePowerIndices Y).filter fun pk => ¬2 ≤ pk.2

def higherPrimePowerReciprocals (Y : ℕ) : ℝ :=
  ∑ pk ∈ higherPrimePowerIndices Y, ((pk.1 ^ pk.2 : ℕ) : ℝ)⁻¹

lemma sum_prime_powers_tail_le {p L : ℕ} (hp : p.Prime) :
    ∑ k ∈ Icc 2 L, ((p ^ k : ℕ) : ℝ)⁻¹ ≤ 2 * ((p : ℝ) ^ 2)⁻¹ := by
  rw [← Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  calc
    ∑ k ∈ range (L + 1 - 2), ((p ^ (2 + k) : ℕ) : ℝ)⁻¹ ≤
        ∑ k ∈ range (L + 1 - 2),
          ((p : ℝ) ^ 2)⁻¹ * (1 / 2 : ℝ) ^ k := by
      apply sum_le_sum
      intro k _hk
      have hpow : (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := by
        exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp.two_le) k
      have hinv : ((p : ℝ) ^ k)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := by
        have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
        rw [inv_le_inv₀ (pow_pos hpR _) (by positivity)]
        exact hpow
      have hsq : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
      calc
        ((p ^ (2 + k) : ℕ) : ℝ)⁻¹ =
            ((p : ℝ) ^ 2)⁻¹ * ((p : ℝ) ^ k)⁻¹ := by
          simp only [pow_add, Nat.cast_mul, Nat.cast_pow, mul_inv]
        _ ≤ ((p : ℝ) ^ 2)⁻¹ * ((2 : ℝ) ^ k)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv hsq
        _ = ((p : ℝ) ^ 2)⁻¹ * (1 / 2 : ℝ) ^ k := by
          rw [one_div_pow]
          norm_num
    _ = ((p : ℝ) ^ 2)⁻¹ *
        ∑ k ∈ range (L + 1 - 2), (1 / 2 : ℝ) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ ((p : ℝ) ^ 2)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ = 2 * ((p : ℝ) ^ 2)⁻¹ := by ring

lemma higherPrimePowerReciprocals_le_two (Y : ℕ) :
    higherPrimePowerReciprocals Y ≤ 2 := by
  calc
    higherPrimePowerReciprocals Y ≤
        ∑ p ∈ Y.primesLE, ∑ k ∈ Icc 2 (Nat.log 2 Y),
          ((p ^ k : ℕ) : ℝ)⁻¹ := by
      simp only [higherPrimePowerReciprocals, higherPrimePowerIndices,
        primePowerIndices, sum_filter]
      calc
        ∑ pk ∈ Y.primesLE ×ˢ Icc 1 (Nat.log 2 Y),
            (if pk.1 ^ pk.2 ≤ Y then
              if 2 ≤ pk.2 then ((pk.1 ^ pk.2 : ℕ) : ℝ)⁻¹ else 0 else 0) ≤
            ∑ pk ∈ Y.primesLE ×ˢ Icc 1 (Nat.log 2 Y),
              if 2 ≤ pk.2 then ((pk.1 ^ pk.2 : ℕ) : ℝ)⁻¹ else 0 := by
          apply sum_le_sum
          intro pk _hpk
          by_cases htwo : 2 ≤ pk.2
          · by_cases hpow : pk.1 ^ pk.2 ≤ Y <;> simp [htwo, hpow]
          · simp [htwo]
        _ = ∑ p ∈ Y.primesLE, ∑ k ∈ Icc 2 (Nat.log 2 Y),
              ((p ^ k : ℕ) : ℝ)⁻¹ := by
          rw [Finset.sum_product]
          apply sum_congr rfl
          intro p _hp
          rw [← sum_filter]
          congr 2
          ext k
          simp only [mem_filter, mem_Icc]
          omega
    _ ≤ ∑ p ∈ Y.primesLE, 2 * ((p : ℝ) ^ 2)⁻¹ := by
      apply sum_le_sum
      intro p hp
      exact sum_prime_powers_tail_le (Nat.prime_of_mem_primesLE hp)
    _ ≤ ∑ n ∈ Ioc 1 Y, 2 * ((n : ℝ) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := Nat.mem_primesLE.mp hp
        exact Finset.mem_Ioc.mpr ⟨hp'.2.one_lt, hp'.1⟩
      · intro n _hn _hnot
        positivity
    _ ≤ 2 := by
      by_cases hY : Y = 0
      · subst Y
        simp
      · have hseries := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := Y)
          one_ne_zero (Nat.one_le_iff_ne_zero.mpr hY)
        norm_num at hseries
        rw [← Finset.mul_sum]
        have hinv : 0 ≤ (Y : ℝ)⁻¹ := by positivity
        calc
          2 * ∑ i ∈ Ioc 1 Y, ((i : ℝ) ^ 2)⁻¹ ≤ 2 * (1 - (Y : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hseries (by norm_num)
          _ ≤ 2 := by nlinarith

lemma sum_firstPrimePowerIndicators {Y n : ℕ} :
    ∑ pk ∈ firstPrimePowerIndices Y, (if pk.1 ^ pk.2 ∣ n then 1 else 0) =
      ∑ p ∈ Y.primesLE, (if p ∣ n then 1 else 0) := by
  apply Finset.sum_bij (fun pk _hpk => pk.1)
  · intro pk hpk
    have hdata := mem_primePowerIndices.mp (mem_filter.mp hpk).1
    exact Nat.mem_primesLE.mpr ⟨hdata.2.1, hdata.1⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    have h₁ := mem_filter.mp ha₁
    have h₂ := mem_filter.mp ha₂
    have hk₁ : a₁.2 = 1 := by
      have := (mem_primePowerIndices.mp h₁.1).2.2.1
      omega
    have hk₂ : a₂.2 = 1 := by
      have := (mem_primePowerIndices.mp h₂.1).2.2.1
      omega
    apply Prod.ext
    · exact heq
    · simp [hk₁, hk₂]
  · intro p hp
    have hpData := Nat.mem_primesLE.mp hp
    have htwoY : 2 ≤ Y := hpData.2.two_le.trans hpData.1
    have hlog : 1 ≤ Nat.log 2 Y :=
      Nat.le_log_of_pow_le Nat.one_lt_two (by simpa using htwoY)
    refine ⟨(p, 1), ?_, rfl⟩
    simp [firstPrimePowerIndices, mem_primePowerIndices, hpData.2, hpData.1, hlog]
  · intro pk hpk
    have hkPos := (mem_primePowerIndices.mp (mem_filter.mp hpk).1).2.2.1
    have hkNot := (mem_filter.mp hpk).2
    have hk : pk.2 = 1 := by omega
    simp [hk]

lemma omega_eq_add_higherPrimePowerIndicators {Y n : ℕ}
    (hnPos : 0 < n) (hnY : n ≤ Y) :
    Ω n = ω n +
      ∑ pk ∈ higherPrimePowerIndices Y, (if pk.1 ^ pk.2 ∣ n then 1 else 0) := by
  let f : ℕ × ℕ → ℕ := fun pk => if pk.1 ^ pk.2 ∣ n then 1 else 0
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (primePowerIndices Y) (fun pk => 2 ≤ pk.2) f
  change (∑ pk ∈ higherPrimePowerIndices Y, f pk) +
      (∑ pk ∈ firstPrimePowerIndices Y, f pk) =
        ∑ pk ∈ primePowerIndices Y, f pk at hsplit
  have hfull : Ω n = ∑ pk ∈ primePowerIndices Y, f pk := by
    simpa only [f] using omega_eq_sum_primePowerIndicators hnPos hnY
  have hlow : ω n = ∑ pk ∈ firstPrimePowerIndices Y, f pk := by
    rw [omega_eq_sum_primeIndicators hnPos hnY]
    simpa only [f] using (sum_firstPrimePowerIndicators (Y := Y) (n := n)).symm
  calc
    Ω n = ∑ pk ∈ primePowerIndices Y, f pk := hfull
    _ = (∑ pk ∈ higherPrimePowerIndices Y, f pk) +
        ∑ pk ∈ firstPrimePowerIndices Y, f pk := hsplit.symm
    _ = ω n + ∑ pk ∈ higherPrimePowerIndices Y, f pk := by
      rw [← hlow]
      omega

lemma omega_le_Omega (n : ℕ) : ω n ≤ Ω n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hY := omega_eq_add_higherPrimePowerIndicators
      (Y := n) (n := n) (Nat.pos_of_ne_zero hn) le_rfl
    omega

lemma omega_sub_eq_higherPrimePowerIndicators {Y n : ℕ}
    (hnPos : 0 < n) (hnY : n ≤ Y) :
    Ω n - ω n =
      ∑ pk ∈ higherPrimePowerIndices Y, (if pk.1 ^ pk.2 ∣ n then 1 else 0) := by
  rw [omega_eq_add_higherPrimePowerIndicators hnPos hnY]
  omega

lemma sum_omegaExcess_eq_sum_div (Y : ℕ) :
    ∑ n ∈ Ioc 0 Y, (Ω n - ω n) =
      ∑ pk ∈ higherPrimePowerIndices Y, Y / (pk.1 ^ pk.2) := by
  calc
    ∑ n ∈ Ioc 0 Y, (Ω n - ω n) =
        ∑ n ∈ Ioc 0 Y, ∑ pk ∈ higherPrimePowerIndices Y,
          (if pk.1 ^ pk.2 ∣ n then 1 else 0) := by
      apply sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      exact omega_sub_eq_higherPrimePowerIndicators hn'.1 hn'.2
    _ = ∑ pk ∈ higherPrimePowerIndices Y, ∑ n ∈ Ioc 0 Y,
          (if pk.1 ^ pk.2 ∣ n then 1 else 0) := by
      rw [sum_comm]
    _ = ∑ pk ∈ higherPrimePowerIndices Y, Y / (pk.1 ^ pk.2) := by
      apply sum_congr rfl
      intro pk _hpk
      rw [← sum_filter, ← card_eq_sum_ones]
      exact Nat.Ioc_filter_dvd_card_eq_div Y (pk.1 ^ pk.2)

lemma omegaExcess_firstMoment_upper (Y : ℕ) :
    ∑ n ∈ Ioc 0 Y, ((Ω n - ω n : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := by
  have hexcess := congrArg (fun z : ℕ => (z : ℝ)) (sum_omegaExcess_eq_sum_div Y)
  simp only [Nat.cast_sum] at hexcess
  rw [hexcess]
  calc
    ∑ pk ∈ higherPrimePowerIndices Y,
          ((Y / (pk.1 ^ pk.2) : ℕ) : ℝ) ≤
      ∑ pk ∈ higherPrimePowerIndices Y,
        (Y : ℝ) * ((pk.1 ^ pk.2 : ℕ) : ℝ)⁻¹ := by
      apply sum_le_sum
      intro pk _hpk
      simpa only [div_eq_mul_inv] using
        (Nat.cast_div_le (α := ℝ) (m := Y) (n := pk.1 ^ pk.2))
    _ = (Y : ℝ) * higherPrimePowerReciprocals Y := by
      rw [higherPrimePowerReciprocals, Finset.mul_sum]
    _ ≤ (Y : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (higherPrimePowerReciprocals_le_two Y) (by positivity)
    _ = 2 * (Y : ℝ) := by ring

def logLogNat (Y : ℕ) : ℝ := Real.log (Real.log (Y : ℝ))

def highOmega (Y : ℕ) : Finset ℕ :=
  (Ioc 0 Y).filter fun n => (7 / 5 : ℝ) * logLogNat Y < (Ω n : ℝ)

lemma highOmega_weight_bound {Y : ℕ}
    (hL : 0 < logLogNat Y)
    (hP : primeReciprocals Y ≤ (139 / 100 : ℝ) * logLogNat Y) :
    ((highOmega Y).card : ℝ) * (logLogNat Y / 200) ^ 2 ≤
      3 * (Y : ℝ) * primeReciprocals Y +
        (logLogNat Y / 200) * (2 * (Y : ℝ)) := by
  let L := logLogNat Y
  let P := primeReciprocals Y
  let t := L / 200
  have ht : 0 < t := by dsimp [t]; positivity
  have hpoint : ∀ n ∈ highOmega Y,
      t ^ 2 ≤ ((ω n : ℝ) - P) ^ 2 + t * (Ω n - ω n : ℕ) := by
    intro n hn
    have hnData := mem_filter.mp hn
    have hnIoc := Finset.mem_Ioc.mp hnData.1
    have hOmega := hnData.2
    have hle := omega_le_Omega n
    have hcastSub : ((Ω n - ω n : ℕ) : ℝ) = (Ω n : ℝ) - (ω n : ℝ) := by
      exact Nat.cast_sub hle
    have hgap : 2 * t < ((ω n : ℝ) - P) + (Ω n - ω n : ℕ) := by
      dsimp [t, L, P]
      rw [hcastSub]
      dsimp [logLogNat] at hOmega hP ⊢
      nlinarith
    by_cases hE : t ≤ ((Ω n - ω n : ℕ) : ℝ)
    · have ht0 : 0 ≤ t := ht.le
      have hprod : t ^ 2 ≤ t * ((Ω n - ω n : ℕ) : ℝ) := by
        nlinarith
      exact hprod.trans (le_add_of_nonneg_left (sq_nonneg _))
    · have hdev : t < (ω n : ℝ) - P := by
        push Not at hE
        nlinarith
      have hsq : t ^ 2 ≤ ((ω n : ℝ) - P) ^ 2 := by nlinarith
      exact hsq.trans (le_add_of_nonneg_right (mul_nonneg ht.le (by positivity)))
  change ((highOmega Y).card : ℝ) * t ^ 2 ≤
    3 * (Y : ℝ) * P + t * (2 * (Y : ℝ))
  calc
    ((highOmega Y).card : ℝ) * t ^ 2 =
        ∑ _n ∈ highOmega Y, t ^ 2 := by simp
    _ ≤ ∑ n ∈ highOmega Y,
        (((ω n : ℝ) - P) ^ 2 + t * (Ω n - ω n : ℕ)) := by
      apply sum_le_sum
      exact hpoint
    _ ≤ ∑ n ∈ Ioc 0 Y,
        (((ω n : ℝ) - P) ^ 2 + t * (Ω n - ω n : ℕ)) := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact filter_subset _ _
      · intro n _hn _hnot
        exact add_nonneg (sq_nonneg _) (mul_nonneg ht.le (by positivity))
    _ = (∑ n ∈ Ioc 0 Y, ((ω n : ℝ) - P) ^ 2) +
        t * ∑ n ∈ Ioc 0 Y, ((Ω n - ω n : ℕ) : ℝ) := by
      rw [sum_add_distrib, Finset.mul_sum]
    _ ≤ 3 * (Y : ℝ) * P + t * (2 * (Y : ℝ)) := by
      exact add_le_add (omega_variance_upper Y)
        (mul_le_mul_of_nonneg_left (omegaExcess_firstMoment_upper Y) ht.le)

lemma eventually_logLogNat_pos : ∀ᶠ Y : ℕ in atTop, 0 < logLogNat Y := by
  have hreal : ∀ᶠ x : ℝ in atTop, Real.exp 1 < x := eventually_gt_atTop _
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal
  filter_upwards [hnat] with Y hY
  have hYpos : 0 < (Y : ℝ) := (Real.exp_pos 1).trans hY
  have hlog : 1 < Real.log (Y : ℝ) := (Real.lt_log_iff_exp_lt hYpos).2 hY
  exact Real.log_pos hlog

lemma eventually_primeReciprocals_le_139 :
    ∀ᶠ Y : ℕ in atTop,
      primeReciprocals Y ≤ (139 / 100 : ℝ) * logLogNat Y := by
  have hcoef : Real.log 4 + (1 / 1000 : ℝ) < 139 / 100 := by
    rw [Real.log_four_eq]
    have hlog := Real.log_two_lt_d9
    norm_num at hlog ⊢
    linarith
  have hreal := eventually_primeReciprocals_le (ε := (1 / 1000 : ℝ)) (by norm_num)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal
  filter_upwards [hnat, eventually_logLogNat_pos] with Y hY hL
  have hY' : primeReciprocals Y ≤
      (Real.log 4 + (1 / 1000 : ℝ)) * logLogNat Y := by
    simpa [logLogNat] using hY
  exact hY'.trans (mul_le_mul_of_nonneg_right hcoef.le hL.le)

lemma highOmega_card_mul_logLog_le {Y : ℕ}
    (hL : 0 < logLogNat Y)
    (hP : primeReciprocals Y ≤ (139 / 100 : ℝ) * logLogNat Y) :
    ((highOmega Y).card : ℝ) * logLogNat Y ≤ 167200 * (Y : ℝ) := by
  let L := logLogNat Y
  let P := primeReciprocals Y
  have hweight := highOmega_weight_bound hL hP
  have hY0 : 0 ≤ (Y : ℝ) := by positivity
  have hPpart : 3 * (Y : ℝ) * P ≤
      3 * (Y : ℝ) * ((139 / 100 : ℝ) * L) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have hrhs :
      3 * (Y : ℝ) * P + (L / 200) * (2 * (Y : ℝ)) ≤
        (209 / 50 : ℝ) * (Y : ℝ) * L := by
    calc
      3 * (Y : ℝ) * P + (L / 200) * (2 * (Y : ℝ)) ≤
          3 * (Y : ℝ) * ((139 / 100 : ℝ) * L) +
            (L / 200) * (2 * (Y : ℝ)) := add_le_add hPpart le_rfl
      _ = (209 / 50 : ℝ) * (Y : ℝ) * L := by ring
  have hscaled : ((highOmega Y).card : ℝ) * L ^ 2 ≤
      167200 * (Y : ℝ) * L := by
    dsimp [L, P] at hweight hrhs ⊢
    nlinarith [hweight.trans hrhs]
  apply (mul_le_mul_iff_left₀ hL).mp
  simpa only [mul_assoc, pow_two] using hscaled

lemma eventually_highOmega_card_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop, ((highOmega Y).card : ℝ) ≤ ε * (Y : ℝ) := by
  have hlittle := Real.one_isLittleO_log_log.bound
    (show 0 < ε / 167200 by positivity)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlittle
  filter_upwards [eventually_logLogNat_pos, eventually_primeReciprocals_le_139, hnat]
    with Y hL hP hlarge
  have hlarge' : (167200 : ℝ) ≤ ε * logLogNat Y := by
    have habsL : |logLogNat Y| = logLogNat Y := abs_of_pos hL
    have habsL' : |Real.log (Real.log (Y : ℝ))| =
        Real.log (Real.log (Y : ℝ)) := by simpa [logLogNat] using habsL
    have hlarge0 : (1 : ℝ) ≤ (ε / 167200) * logLogNat Y := by
      simpa [Real.norm_eq_abs, logLogNat, habsL'] using hlarge
    nlinarith
  have hcardL := highOmega_card_mul_logLog_le hL hP
  have hY0 : 0 ≤ (Y : ℝ) := by positivity
  have hlargeY := mul_le_mul_of_nonneg_right hlarge' hY0
  apply (mul_le_mul_iff_left₀ hL).mp
  calc
    ((highOmega Y).card : ℝ) * logLogNat Y ≤ 167200 * (Y : ℝ) := hcardL
    _ ≤ (ε * (Y : ℝ)) * logLogNat Y := by
      nlinarith

/-! ## Reciprocal primes in a multiplicative short interval -/

lemma primeReciprocals_sub_le_loglog {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, 3 ≤ T ∧ ∀ Y N : ℕ, T ≤ (Y : ℝ) → Y ≤ N →
      primeReciprocals N - primeReciprocals Y ≤
        (Real.log 4 + δ) / Real.log (N : ℝ) +
          (Real.log 4 + δ) *
            (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (Y : ℝ))) := by
  let K := Real.log 4 + δ
  have hK : 0 < K := add_pos (Real.log_pos (by norm_num)) hδ
  have hpi := Chebyshev.eventually_primeCounting_le hδ
  rw [eventually_atTop] at hpi
  obtain ⟨T₀, hT₀⟩ := hpi
  let T := max T₀ (max 3 (Real.exp 1))
  have hT3 : 3 ≤ T := le_max_of_le_right (le_max_left _ _)
  have hT0 : T₀ ≤ T := le_max_left _ _
  refine ⟨T, hT3, ?_⟩
  intro Y N hTY hYN
  have hY3 : 3 ≤ (Y : ℝ) := hT3.trans hTY
  have hN3 : 3 ≤ (N : ℝ) := hY3.trans (by exact_mod_cast hYN)
  have hYNreal : (Y : ℝ) ≤ N := by exact_mod_cast hYN
  have hpiN := hT₀ (N : ℝ) (hT0.trans (hTY.trans hYNreal))
  have hNpos : 0 < (N : ℝ) := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hboundary : (Nat.primeCounting N : ℝ) / (N : ℝ) ≤ K / Real.log (N : ℝ) := by
    simpa only [Nat.floor_natCast] using (calc
      (Nat.primeCounting ⌊(N : ℝ)⌋₊ : ℝ) / (N : ℝ) ≤
          (K * (N : ℝ) / Real.log (N : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right hpiN hNpos.le
      _ = K / Real.log (N : ℝ) := by field_simp)
  let f : ℝ → ℝ := fun t => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2
  have hInt2Y : IntervalIntegrable f volume 2 (Y : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    simpa [f] using integrableOn_primeCounting_div_sq (Y : ℝ)
  have hIntYN : IntervalIntegrable f volume (Y : ℝ) (N : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hYNreal]
    apply (integrableOn_primeCounting_div_sq (N : ℝ)).mono_set
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  have hmajor :
      ∫ t in (Y : ℝ)..(N : ℝ), f t ≤
        K * (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (Y : ℝ))) := by
    calc
      ∫ t in (Y : ℝ)..(N : ℝ), f t ≤
          ∫ t in (Y : ℝ)..(N : ℝ), K * (t⁻¹ / Real.log t) := by
        refine intervalIntegral.integral_mono_on hYNreal hIntYN ?_ ?_
        · refine ContinuousOn.intervalIntegrable fun t ht =>
            ContinuousAt.continuousWithinAt ?_
          rw [Set.uIcc_of_le hYNreal] at ht
          have ht1 : 1 < t := by linarith [hY3, ht.1]
          have ht0 : t ≠ 0 := by linarith
          have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
          fun_prop
        · intro t ht
          rw [Set.mem_Icc] at ht
          have htT0 : T₀ ≤ t := hT0.trans (hTY.trans ht.1)
          have htPos : 0 < t := by linarith [hY3, ht.1]
          have hp := hT₀ t htT0
          dsimp [f]
          calc
            (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤
                (K * t / Real.log t) / t ^ 2 :=
              div_le_div_of_nonneg_right hp (sq_nonneg t)
            _ = K * (t⁻¹ / Real.log t) := by field_simp
      _ = K * (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (Y : ℝ))) := by
        rw [intervalIntegral.integral_const_mul,
          integral_inv_div_log (by linarith) (by linarith)]
  have hpiYnonneg : 0 ≤ (Nat.primeCounting Y : ℝ) / (Y : ℝ) := by positivity
  have hAbelN : primeReciprocals N = (Nat.primeCounting N : ℝ) / (N : ℝ) +
      ∫ t in 2..(N : ℝ), f t := by
    simpa [f] using
      (primeReciprocals_eq_primeCounting_div_add_integral (x := (N : ℝ)) (by linarith))
  have hAbelY : primeReciprocals Y = (Nat.primeCounting Y : ℝ) / (Y : ℝ) +
      ∫ t in 2..(Y : ℝ), f t := by
    simpa [f] using
      (primeReciprocals_eq_primeCounting_div_add_integral (x := (Y : ℝ)) (by linarith))
  rw [hAbelN, hAbelY,
    ← intervalIntegral.integral_add_adjacent_intervals hInt2Y hIntYN]
  dsimp [f] at hmajor ⊢
  nlinarith

end

end Erdos784.Analytic
