/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperClusterMass
import ErdosProblems.Erdos446.ScaleAsymptotics
import ErdosProblems.Erdos446.PrimeBlocks

/-!
# Erdős Problem 446: the high prime-factor tail

The elementary squarefree estimate gives a Poisson majorant with parameter
twice the reciprocal-prime mass.  This file proves that the layers with more
than ten times the selected Ford depth are negligible.  The proof is fully
finite: exponential tilting by `2^k` bounds an arbitrary finite tail by an
exponential series, the proved reciprocal-prime Mertens estimate bounds its
parameter by the selected depth, and elementary numerical estimates compare
the resulting geometric decay with `fordCombinatorialWeight`.
-/

namespace Erdos446

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-- The reciprocal mass of the primes in `primesUpTo P`. -/
def smoothPrimeReciprocalMass (P : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo P, 1 / (p : ℝ)

theorem smoothPrimeReciprocalMass_eq_primeHarmonic (P : ℕ) :
    smoothPrimeReciprocalMass P = Erdos697.PrimeHarmonic.sum P := by
  rw [smoothPrimeReciprocalMass, Erdos697.PrimeHarmonic.sum]
  apply Finset.sum_congr
  · ext p
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hp2, hpP⟩, hp⟩
      exact ⟨hpP, hp⟩
    · rintro ⟨hpP, hp⟩
      exact ⟨⟨hp.two_le, hpP⟩, hp⟩
  · intro p hp
    rw [one_div]

/-- Exponential tilting bounds every finite Poisson tail. -/
theorem finite_poisson_tail_le_exp_div_two_pow
    {x : ℝ} (hx : 0 ≤ x) (n J : ℕ) :
    (∑ k ∈ Finset.Ioc n J, x ^ k / (k.factorial : ℝ)) ≤
      Real.exp (2 * x) / (2 : ℝ) ^ n := by
  have hterm : ∀ k ∈ Finset.Ioc n J,
      x ^ k / (k.factorial : ℝ) ≤
        ((2 * x) ^ k / (k.factorial : ℝ)) / (2 : ℝ) ^ n := by
    intro k hk
    have hnk : n ≤ k := (Finset.mem_Ioc.mp hk).1.le
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ k := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hnk
    have hnum : 0 ≤ (2 * x) ^ k / (k.factorial : ℝ) := by
      positivity
    calc
      x ^ k / (k.factorial : ℝ) =
          ((2 * x) ^ k / (k.factorial : ℝ)) / (2 : ℝ) ^ k := by
        rw [mul_pow]
        field_simp
      _ ≤ ((2 * x) ^ k / (k.factorial : ℝ)) / (2 : ℝ) ^ n := by
        exact div_le_div_of_nonneg_left hnum (by positivity) hpow
  calc
    (∑ k ∈ Finset.Ioc n J, x ^ k / (k.factorial : ℝ)) ≤
        ∑ k ∈ Finset.Ioc n J,
          ((2 * x) ^ k / (k.factorial : ℝ)) / (2 : ℝ) ^ n :=
      Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.Ioc n J,
          (2 * x) ^ k / (k.factorial : ℝ)) / (2 : ℝ) ^ n := by
      rw [Finset.sum_div]
    _ ≤ (∑ k ∈ Finset.range (J + 1),
          (2 * x) ^ k / (k.factorial : ℝ)) / (2 : ℝ) ^ n := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2
      · intro k hkRange hkTail
        positivity
    _ ≤ Real.exp (2 * x) / (2 : ℝ) ^ n := by
      exact div_le_div_of_nonneg_right
        (Real.sum_le_exp_of_nonneg (by positivity) (J + 1)) (by positivity)

/-- The Mertens parameter at the cutoff `2y` is eventually no larger than
the selected Ford depth.  The leading coefficient is `log 2 < 1`; all fixed
Mertens and scale constants are absorbed after the depth tends to infinity.
-/
theorem eventually_smoothPrimeReciprocalMass_two_mul_le_depth (M : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      smoothPrimeReciprocalMass (2 * y) ≤ (fordScaleDepth M y : ℝ) := by
  obtain ⟨C, hC, hMertens⟩ := exists_primeHarmonic_sharp_error
  rw [eventually_atTop] at hMertens
  obtain ⟨N, hN⟩ := hMertens
  let c := fordScaleConstant M
  let A : ℝ := |Real.log (4 * c)| + |meissel_mertens| + 1
  have hc : 0 < c := fordScaleConstant_pos M
  have hgap : 0 < 1 - Real.log 2 := by
    linarith [Real.log_two_lt_d9]
  have hdepthAbsorb : ∀ᶠ y : ℕ in atTop,
      A ≤ (1 - Real.log 2) * (fordScaleDepth M y : ℝ) := by
    have htop := (tendsto_fordScaleDepth_cast_atTop M).eventually
      (eventually_ge_atTop (A / (1 - Real.log 2)))
    filter_upwards [htop] with y hy
    have := (div_le_iff₀ hgap).mp hy
    nlinarith
  have hlogTop : Tendsto
      (fun y : ℕ ↦ Real.log (((2 * y : ℕ) : ℝ))) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    apply tendsto_natCast_atTop_atTop.comp
    refine Filter.tendsto_atTop_mono' atTop (f₁ := fun y : ℕ ↦ y) ?_ tendsto_id
    filter_upwards with y
    omega
  have herrorSmall : ∀ᶠ y : ℕ in atTop,
      C / Real.log (((2 * y : ℕ) : ℝ)) ≤ 1 := by
    have hlarge := hlogTop.eventually (eventually_ge_atTop C)
    filter_upwards [hlarge, eventually_ge_atTop 1] with y hy hy1
    have hlogPos : 0 < Real.log (((2 * y : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < 2 * y by omega)
    exact (div_le_one hlogPos).2 hy
  filter_upwards [eventually_ge_atTop (max (fordConstructionScale M 1) (max N 2)),
      hdepthAbsorb, herrorSmall]
      with y hy hAbsorb hErr
  let K := fordScaleDepth M y
  have hyScale : fordConstructionScale M 1 ≤ y :=
    (le_max_left _ _).trans hy
  have hyN : N ≤ 2 * y := by
    have hinner : max N 2 ≤ y := (le_max_right _ _).trans hy
    have : N ≤ y := (le_max_left _ _).trans hinner
    omega
  have hy2 : 2 ≤ y :=
    (le_max_right N 2).trans ((le_max_right _ _).trans hy)
  have hKpos : 0 < K := fordScaleDepth_pos hyScale
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogTwoLe : Real.log 2 ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hy2)
  let L : ℝ := Real.log (((2 * y : ℕ) : ℝ))
  have hlogMul : L =
      Real.log 2 + Real.log (y : ℝ) := by
    dsimp [L]
    push_cast
    rw [Real.log_mul (by norm_num)
      (by exact_mod_cast (show y ≠ 0 by omega))]
  have hlogTwoY : L ≤
      4 * c * (2 : ℝ) ^ K := by
    rw [hlogMul]
    have hscale := (fordScaleDepth_log_bounds hyScale).2
    nlinarith
  have hfourPos : 0 < 4 * c * (2 : ℝ) ^ K := by positivity
  have hloglog : Real.log L ≤
      Real.log (4 * c) + (K : ℝ) * Real.log 2 := by
    calc
      Real.log L ≤ Real.log (4 * c * (2 : ℝ) ^ K) :=
        Real.log_le_log (by rw [hlogMul]; positivity) hlogTwoY
      _ = Real.log (4 * c) + (K : ℝ) * Real.log 2 := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hMer := hN (2 * y) hyN
  rw [← smoothPrimeReciprocalMass_eq_primeHarmonic] at hMer
  change |smoothPrimeReciprocalMass (2 * y) -
      (Real.log L + meissel_mertens)| ≤ C / L at hMer
  have hmain : smoothPrimeReciprocalMass (2 * y) ≤
      Real.log L + meissel_mertens + C / L := by
    linarith [le_abs_self
      (smoothPrimeReciprocalMass (2 * y) -
        (Real.log L + meissel_mertens))]
  have hconst : Real.log (4 * c) + meissel_mertens + 1 ≤ A := by
    dsimp [A]
    linarith [le_abs_self (Real.log (4 * c)), le_abs_self meissel_mertens]
  calc
    smoothPrimeReciprocalMass (2 * y) ≤
        Real.log L + meissel_mertens + C / L := hmain
    _ ≤ (Real.log (4 * c) + (K : ℝ) * Real.log 2) +
          meissel_mertens + 1 := by linarith
    _ ≤ A + (K : ℝ) * Real.log 2 := by linarith
    _ ≤ (K : ℝ) := by
      dsimp [K] at hAbsorb ⊢
      linarith

/-- The finite sum of squarefree layers strictly above `10K`. -/
def highSquarefreeClusterTail (M y : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc (10 * fordScaleDepth M y) (primesUpTo (2 * y)).card,
    squarefreeClusterLayer (2 * y) k

private theorem exp_four_le_sixtyfour : Real.exp 4 ≤ 64 := by
  have hfour : (4 : ℝ) ≤ 6 * Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  rw [← hlog] at hfour
  have := Real.exp_le_exp.mpr hfour
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 64)] using this

private theorem high_tail_numerical_le_inv
    {K : ℕ} (hK : 0 < K) :
    Real.log 2 * Real.exp (4 * (K : ℝ)) / (2 : ℝ) ^ (10 * K) ≤
      1 / (K : ℝ) := by
  have hExpEq : Real.exp (4 * (K : ℝ)) = Real.exp 4 ^ K := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hExp : Real.exp (4 * (K : ℝ)) ≤ (64 : ℝ) ^ K := by
    rw [hExpEq]
    exact pow_le_pow_left₀ (Real.exp_pos 4).le exp_four_le_sixtyfour K
  have hPow : (64 : ℝ) ^ K * (2 : ℝ) ^ (4 * K) =
      (2 : ℝ) ^ (10 * K) := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogOne : Real.log 2 ≤ 1 := (Real.log_two_lt_d9.trans (by norm_num)).le
  have hKpow : (K : ℝ) ≤ (2 : ℝ) ^ (4 * K) := by
    have hn : K ≤ 2 ^ K := K.lt_two_pow_self.le
    have hp : 2 ^ K ≤ 2 ^ (4 * K) := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast hn.trans hp
  have hden : 0 < (2 : ℝ) ^ (10 * K) := by positivity
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  apply (div_le_iff₀ hden).2
  rw [one_div, inv_mul_eq_div]
  apply (le_div_iff₀ hKR).2
  calc
    (Real.log 2 * Real.exp (4 * (K : ℝ))) * (K : ℝ) =
        (K : ℝ) * (Real.log 2 * Real.exp (4 * (K : ℝ))) := by ring
    _ = ((K : ℝ) * Real.log 2) * Real.exp (4 * (K : ℝ)) := by ring
    _ ≤
        (2 : ℝ) ^ (4 * K) * (1 * (64 : ℝ) ^ K) := by
      have hKlog : (K : ℝ) * Real.log 2 ≤ (2 : ℝ) ^ (4 * K) := by
        calc
          (K : ℝ) * Real.log 2 ≤ (2 : ℝ) ^ (4 * K) * 1 :=
            mul_le_mul hKpow hlogOne hlog (by positivity)
          _ = (2 : ℝ) ^ (4 * K) := mul_one _
      simpa only [one_mul] using
        mul_le_mul hKlog hExp (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (10 * K) := by rw [one_mul, mul_comm, hPow]

private theorem fordCombinatorialWeight_ge_inv
    {K : ℕ} (hK : 0 < K) :
    1 / (K : ℝ) ≤ fordCombinatorialWeight K := by
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hfac : (K.factorial : ℝ) ≤ (K : ℝ) ^ K := by
    exact_mod_cast Nat.factorial_le_pow K
  have hpowPred : (K : ℝ) ^ K = (K : ℝ) ^ (K - 1) * K := by
    calc
      (K : ℝ) ^ K = (K : ℝ) ^ ((K - 1) + 1) := by congr 1; omega
      _ = (K : ℝ) ^ (K - 1) * K := by rw [pow_succ]
  have hquot : 1 / (K : ℝ) ≤
      (K : ℝ) ^ (K - 1) / (K.factorial : ℝ) := by
    have hfacPos : (0 : ℝ) < K.factorial := by positivity
    apply (div_le_div_iff₀ hKR hfacPos).2
    calc
      1 * (K.factorial : ℝ) = (K.factorial : ℝ) := one_mul _
      _ ≤ (K : ℝ) ^ K := hfac
      _ = (K : ℝ) ^ (K - 1) * K := hpowPred
  have hbase : 1 ≤ 2 * Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hbasePow : 1 ≤ (2 * Real.log 2 : ℝ) ^ K := one_le_pow₀ hbase
  have hquotNonneg : 0 ≤
      (K : ℝ) ^ (K - 1) / (K.factorial : ℝ) := by positivity
  calc
    1 / (K : ℝ) ≤
        (K : ℝ) ^ (K - 1) / (K.factorial : ℝ) := hquot
    _ ≤ (2 * Real.log 2 : ℝ) ^ K *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hbasePow hquotNonneg
    _ = fordCombinatorialWeight K := rfl

/-- Ford's high-prime-factor tail is eventually bounded by the central
combinatorial weight, with constant one and no analytic assumptions. -/
theorem eventually_highSquarefreeClusterTail_le_fordCombinatorialWeight
    (M : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      highSquarefreeClusterTail M y ≤
        fordCombinatorialWeight (fordScaleDepth M y) := by
  filter_upwards [eventually_smoothPrimeReciprocalMass_two_mul_le_depth M,
      eventually_ge_atTop (fordConstructionScale M 1)]
      with y hmass hyScale
  let K := fordScaleDepth M y
  let S := smoothPrimeReciprocalMass (2 * y)
  have hK : 0 < K := fordScaleDepth_pos hyScale
  have hS : 0 ≤ S := by
    dsimp [S, smoothPrimeReciprocalMass]
    positivity
  have hPoisson := finite_poisson_tail_le_exp_div_two_pow
    (x := 2 * S) (by positivity) (10 * K) (primesUpTo (2 * y)).card
  have hLayer : highSquarefreeClusterTail M y ≤
      Real.log 2 *
        (∑ k ∈ Finset.Ioc (10 * K) (primesUpTo (2 * y)).card,
          (2 * S) ^ k / (k.factorial : ℝ)) := by
    rw [highSquarefreeClusterTail, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have h := squarefreeClusterLayer_le_poissonTerm (2 * y) k
    rw [mul_div_assoc] at h
    simpa only [S, smoothPrimeReciprocalMass] using h
  have hExpMono : Real.exp (2 * (2 * S)) ≤
      Real.exp (4 * (K : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [S, K] at hmass ⊢
    nlinarith
  calc
    highSquarefreeClusterTail M y ≤
        Real.log 2 *
          (∑ k ∈ Finset.Ioc (10 * K) (primesUpTo (2 * y)).card,
            (2 * S) ^ k / (k.factorial : ℝ)) := hLayer
    _ ≤ Real.log 2 *
        (Real.exp (2 * (2 * S)) / (2 : ℝ) ^ (10 * K)) := by
      exact mul_le_mul_of_nonneg_left hPoisson
        (Real.log_nonneg (by norm_num))
    _ ≤ Real.log 2 * Real.exp (4 * (K : ℝ)) /
        (2 : ℝ) ^ (10 * K) := by
      rw [mul_div_assoc]
      have hden : 0 < (2 : ℝ) ^ (10 * K) := by positivity
      apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
      exact (div_le_div_iff_of_pos_right hden).2 hExpMono
    _ ≤ 1 / (K : ℝ) := high_tail_numerical_le_inv hK
    _ ≤ fordCombinatorialWeight K := fordCombinatorialWeight_ge_inv hK

end

end Erdos446
