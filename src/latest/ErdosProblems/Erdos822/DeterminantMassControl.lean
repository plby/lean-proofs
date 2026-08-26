/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B5InputSize
import ErdosProblems.Erdos822.LogFiberMajorant

/-!
# Uniform cancellation of the determinant prime mass

The divisor reciprocal mass is bounded by the full one-shift prime mass.
That mass is at most the logarithm of the inverse one-shift Euler product.
After exponentiating, the resulting square inverse product is exactly
cancelled by the square logarithm ratio already present in the fiber
majorant.
-/

namespace Erdos822

open scoped BigOperators

/-- A divisor-restricted reciprocal prime mass is no larger than the full
one-shift density mass. -/
theorem divisorReciprocalMass_le_sum_oneShiftDensity
    (h z y : ℕ) :
    divisorReciprocalMass h z y ≤
      ∑ p ∈ Erdos851.sievePrimes z y,
        Erdos851.oneShiftDensity p := by
  unfold divisorReciprocalMass
  apply Finset.sum_le_sum
  intro p hp
  by_cases hph : p ∣ h
  · simp [hph, Erdos851.oneShiftDensity, one_div]
  · simp [hph, Erdos851.oneShiftDensity]

/-- The determinant exponential is bounded by the square inverse
one-shift Euler product. -/
theorem exp_two_divisorReciprocalMass_le_inverseProduct_sq
    (h z y : ℕ) (hz : 2 ≤ z) :
    Real.exp (2 * divisorReciprocalMass h z y) ≤
      Erdos851.inverseLocalEulerProduct
        Erdos851.oneShiftDensity z y ^ 2 := by
  let V := Erdos851.inverseLocalEulerProduct
    Erdos851.oneShiftDensity z y
  have hVpos : 0 < V := by
    dsimp [V, Erdos851.inverseLocalEulerProduct]
    apply Finset.prod_pos
    intro p hp
    exact inv_pos.mpr
      (sub_pos.mpr
        (Erdos851.oneShiftDensity_lt_one
          (Erdos851.mem_sievePrimes.mp hp).2.2))
  have hmass :
      divisorReciprocalMass h z y ≤ Real.log V := by
    calc
      divisorReciprocalMass h z y ≤
          ∑ p ∈ Erdos851.sievePrimes z y,
            Erdos851.oneShiftDensity p :=
        divisorReciprocalMass_le_sum_oneShiftDensity h z y
      _ ≤ Real.log V := by
        dsimp [V]
        apply Erdos851.sum_density_le_log_inverseLocalEulerProduct
        intro p hp
        exact Erdos851.oneShiftDensity_lt_one
          (Erdos851.mem_sievePrimes.mp hp).2.2
  calc
    Real.exp (2 * divisorReciprocalMass h z y) ≤
        Real.exp (2 * Real.log V) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ = V ^ 2 := by
      rw [show 2 * Real.log V = Real.log V + Real.log V by ring,
        Real.exp_add, Real.exp_log hVpos]
      ring

/-- The square Mertens ratio cancels the determinant exponential uniformly
over all determinants and endpoints. -/
theorem exists_logRatio_sq_mul_exp_divisorMass_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ h z y : ℕ, 2 ≤ z → z ≤ y →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          Real.exp (2 * divisorReciprocalMass h z y) ≤
            C ^ 2 := by
  obtain ⟨C, hC, hdim⟩ := Erdos851.exists_oneShift_dimension_bound
  refine ⟨C, hC, ?_⟩
  intro h z y hz hzy
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hratio0 :
      0 ≤ (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 :=
    sq_nonneg _
  have hexp :=
    exp_two_divisorReciprocalMass_le_inverseProduct_sq h z y hz
  have hdim' :
      Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y ^ 2 ≤
        (C * (Real.log (y : ℝ) / Real.log (z : ℝ))) ^ 2 := by
    have hInv0 :
        0 ≤ Erdos851.inverseLocalEulerProduct
          Erdos851.oneShiftDensity z y := by
      unfold Erdos851.inverseLocalEulerProduct
      apply Finset.prod_nonneg
      intro p hp
      exact inv_nonneg.mpr (sub_nonneg.mpr
        (Erdos851.oneShiftDensity_lt_one
          (Erdos851.mem_sievePrimes.mp hp).2.2).le)
    have hright0 :
        0 ≤ C * (Real.log (y : ℝ) / Real.log (z : ℝ)) :=
      mul_nonneg hC.le (div_nonneg hlogy.le hlogz.le)
    exact (sq_le_sq₀
      hInv0 hright0).2 (hdim z y hz hzy)
  calc
    (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        Real.exp (2 * divisorReciprocalMass h z y) ≤
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          Erdos851.inverseLocalEulerProduct
            Erdos851.oneShiftDensity z y ^ 2 :=
      mul_le_mul_of_nonneg_left hexp hratio0
    _ ≤ (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (C * (Real.log (y : ℝ) / Real.log (z : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hdim' hratio0
    _ = C ^ 2 := by
      field_simp

end Erdos822
