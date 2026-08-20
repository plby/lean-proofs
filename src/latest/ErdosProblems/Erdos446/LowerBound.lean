/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.LowerModelAsymptotic
import ErdosProblems.Erdos446.EulerEstimate

/-!
# Erdős Problem 446: the eventual lower bound

This file connects the explicit finite construction to its asymptotic model.
The weak Mertens estimate supplies the second inverse logarithm.  The result is
the lower half of Ford's theorem: `growth446 = O(epsilon)`.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

noncomputable def fordCloseConstant (M : ℕ) : ℝ :=
  2 + 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)

noncomputable def fordLowerConstant (M : ℕ) : ℝ :=
  1 / (768 * Real.exp 1 * fordCloseConstant M)

theorem fordCloseConstant_pos (M : ℕ) : 0 < fordCloseConstant M := by
  dsimp [fordCloseConstant]
  positivity

theorem fordLowerConstant_pos (M : ℕ) : 0 < fordLowerConstant M := by
  dsimp [fordLowerConstant]
  exact one_div_pos.mpr (mul_pos (by positivity) (fordCloseConstant_pos M))

/-- The literal left side produced by the finite lower construction after the
analytic parameters have been fixed. -/
noncomputable def fordFiniteLower (M K y : ℕ) : ℝ :=
  smallPrimeEulerDensity (2 * y) *
    (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
      ((((2 * Real.log 2 : ℝ) ^ K / 2) ^ 2 /
        ((2 * Real.log 2 : ℝ) ^ K * Real.exp 1 *
          fordCloseConstant M)) *
        ((1 / 2 : ℝ) *
          ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)))))

theorem fordFiniteLower_eq {M K y : ℕ}
    (hylog : Real.log (y : ℝ) ≠ 0) :
    fordFiniteLower M K y =
      smallPrimeEulerDensity (2 * y) *
        (fordLowerConstant M *
          (fordCombinatorialWeight K / Real.log (y : ℝ))) := by
  have hbase : (2 * Real.log 2 : ℝ) ^ K ≠ 0 := by positivity
  dsimp [fordFiniteLower, fordLowerConstant, fordCloseConstant,
    fordCombinatorialWeight]
  field_simp [hbase, hylog]
  ring

theorem exists_uniform_fordFiniteLower :
    ∃ N M : ℕ, ∃ C : ℝ,
      3 ≤ N ∧ 3 ≤ M ∧ N ≤ M ∧ 0 < C ∧
      ∀ K y : ℕ, 0 < K → fordConstructionScale M K ≤ y →
        fordFiniteLower M K y ≤ epsilon y (2 * y) := by
  obtain ⟨N, M, C, hN, hM, hNM, hC, h⟩ :=
    exists_uniform_ford_sized_dyadic_lower
  refine ⟨N, M, C, hN, hM, hNM, hC, ?_⟩
  intro K y hK hy
  simpa only [fordFiniteLower, fordCloseConstant] using h K y hK hy

theorem fordCombinatorialDensity_isBigO_finiteLower (M : ℕ) :
    (fun y : ℕ ↦
      fordCombinatorialWeight (fordScaleDepth M y) /
        Real.log (y : ℝ) ^ 2) =O[atTop]
      (fun y : ℕ ↦ fordFiniteLower M (fordScaleDepth M y) y) := by
  let c := fordLowerConstant M
  let A := cleanMertensConstant446
  have hc : 0 < c := fordLowerConstant_pos M
  have hA : 0 < A := cleanMertensConstant446_pos
  apply Asymptotics.IsBigO.of_bound (2 * A / c)
  filter_upwards [eventually_ge_atTop (max 2 (fordConstructionScale M 1))]
    with y hy
  have hy2 : 2 ≤ y := (le_max_left _ _).trans hy
  have hscale : fordConstructionScale M 1 ≤ y :=
    (le_max_right _ _).trans hy
  let K := fordScaleDepth M y
  have hK : 0 < K := fordScaleDepth_pos hscale
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have h2y : 2 ≤ 2 * y := by omega
  have hlog2y : 0 < Real.log (2 * y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * y by omega))
  have hlog2le : Real.log (2 * y : ℝ) ≤ 2 * Real.log (y : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have hlog2lelogy : Real.log 2 ≤ Real.log (y : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hy2)
    linarith
  have heuler : 1 / (A * Real.log (2 * y : ℝ)) ≤
      smallPrimeEulerDensity (2 * y) := by
    simpa only [A, Nat.cast_mul, Nat.cast_ofNat] using
      smallPrimeEulerDensity_lower (2 * y) h2y
  have hden : A * Real.log (2 * y : ℝ) ≤
      2 * A * Real.log (y : ℝ) := by
    dsimp [A]
    nlinarith
  have heuler' : 1 / (2 * A * Real.log (y : ℝ)) ≤
      smallPrimeEulerDensity (2 * y) := by
    exact (one_div_le_one_div_of_le (by positivity) hden).trans heuler
  have hw : 0 ≤ fordCombinatorialWeight K := by
    dsimp [fordCombinatorialWeight]
    positivity
  have heulerNonneg := smallPrimeEulerDensity_nonneg (2 * y)
  have hfiniteNonneg : 0 ≤ fordFiniteLower M K y := by
    rw [fordFiniteLower_eq hlog.ne']
    exact mul_nonneg heulerNonneg
      (mul_nonneg hc.le (div_nonneg hw hlog.le))
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hw (sq_nonneg _)), Real.norm_eq_abs,
    abs_of_nonneg hfiniteNonneg]
  rw [fordFiniteLower_eq hlog.ne']
  change fordCombinatorialWeight K / Real.log (y : ℝ) ^ 2 ≤
    (2 * A / c) *
      (smallPrimeEulerDensity (2 * y) *
        (c * (fordCombinatorialWeight K / Real.log (y : ℝ))))
  calc
    fordCombinatorialWeight K / Real.log (y : ℝ) ^ 2 =
        (2 * A / c) *
          ((1 / (2 * A * Real.log (y : ℝ))) *
            (c * (fordCombinatorialWeight K / Real.log (y : ℝ)))) := by
      field_simp [hA.ne', hc.ne', hlog.ne']
    _ ≤ (2 * A / c) *
        (smallPrimeEulerDensity (2 * y) *
          (c * (fordCombinatorialWeight K / Real.log (y : ℝ)))) := by
      gcongr

theorem fordDepthDensityModel_isBigO_epsilon (M : ℕ)
    (hlower : ∀ᶠ y : ℕ in atTop,
      fordFiniteLower M (fordScaleDepth M y) y ≤ epsilon y (2 * y)) :
    fordDepthDensityModel M =O[atTop]
      (fun y : ℕ ↦ epsilon y (2 * y)) := by
  have hcoeff := fordCombinatorialWeight_depth_isTheta_depthModel M
  have hinv :
      (fun y : ℕ ↦ (Real.log (y : ℝ) ^ 2)⁻¹) =O[atTop]
        (fun y : ℕ ↦ (Real.log (y : ℝ) ^ 2)⁻¹) :=
    isBigO_refl _ _
  have hmodel := hcoeff.2.mul hinv
  have hmodel' : fordDepthDensityModel M =O[atTop]
      (fun y : ℕ ↦
        fordCombinatorialWeight (fordScaleDepth M y) /
          Real.log (y : ℝ) ^ 2) := by
    apply hmodel.congr'
    · filter_upwards [] with y
      dsimp [fordDepthDensityModel]
      rw [div_eq_mul_inv]
    · filter_upwards [] with y
      rw [div_eq_mul_inv]
  have hfinite := fordCombinatorialDensity_isBigO_finiteLower M
  have heps :
      (fun y : ℕ ↦ fordFiniteLower M (fordScaleDepth M y) y) =O[atTop]
        (fun y : ℕ ↦ epsilon y (2 * y)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hlower, eventually_ge_atTop 2] with y hy hy2
    have hlog : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hw : 0 ≤ fordCombinatorialWeight (fordScaleDepth M y) := by
      dsimp [fordCombinatorialWeight]
      positivity
    have hfiniteNonneg : 0 ≤ fordFiniteLower M (fordScaleDepth M y) y := by
      rw [fordFiniteLower_eq hlog.ne']
      exact mul_nonneg (smallPrimeEulerDensity_nonneg _)
        (mul_nonneg (fordLowerConstant_pos M).le (div_nonneg hw hlog.le))
    have hepsNonneg := epsilon_nonneg y (2 * y)
    simpa [Real.norm_eq_abs, abs_of_nonneg hfiniteNonneg,
      abs_of_nonneg hepsNonneg] using hy
  exact hmodel'.trans (hfinite.trans heps)

/-- Ford's construction gives the lower half of the final order estimate. -/
theorem growth446_isBigO_epsilon :
    growth446 =O[atTop] (fun y : ℕ ↦ epsilon y (2 * y)) := by
  obtain ⟨N, M, C, hN, hM, hNM, hC, hlower⟩ :=
    exists_uniform_fordFiniteLower
  have hlowerEv : ∀ᶠ y : ℕ in atTop,
      fordFiniteLower M (fordScaleDepth M y) y ≤ epsilon y (2 * y) := by
    filter_upwards [eventually_ge_atTop (fordConstructionScale M 1)]
      with y hy
    exact hlower _ _ (fordScaleDepth_pos hy) (fordScaleDepth_scale_le hy)
  exact (fordDepthDensityModel_isTheta_growth446 M).2.trans
    (fordDepthDensityModel_isBigO_epsilon M hlowerEv)

end Erdos446
