/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceStageErrorBudgets
import ErdosProblems.Erdos207.InitialMasterErrorPowers
import ErdosProblems.Erdos207.ReserveRegularizationPowerScalars

/-! # One local threshold supplies both actual sparse-prior exceptional budgets -/

namespace Erdos207

open Finset
open scoped NNReal

theorem eventually_source_sparse_prior_budgets
    (q c R m lower : ℕ) (Cdegree Cprior B0 : ℝ≥0) (hc : 1 ≤ c) (hm : 1 ≤ m) :
    ∃ T : ℕ, lower ≤ T ∧ 2 ≤ T ∧ ∀ u : ℕ, T ≤ u → ∀ t : ℝ≥0,
      0 < t → t ≤ (u : ℝ≥0)^c →
      let delta := 1/(u : ℝ≥0)^(c*m)
      let band := 1/(u : ℝ≥0)^(c*m+3*c)
      0 < delta ∧ delta < 1 ∧ delta ≤ 1/t^m ∧ (1/2 : ℝ≥0)^u ≤ delta ∧
      (∀ n : ℕ, n ≤ u^R →
        2*((n : ℝ≥0)^2+(q+1 : ℝ≥0)^2*(n : ℝ≥0)^3)*(1/2 : ℝ≥0)^u ≤ band) ∧
      sourceAllAuxiliaryDegreeFailure q (3*R+3*c) u (3*c) Cdegree B0 ≤ 1/t^2 ∧
      (((Icc 4 q).card : ℝ≥0)/(u : ℝ≥0)^(c*m+3*c)+band+
        sourceSparseCrudeFailure q (6*R+(c*m+3*c)) (Icc 4 q).card u (c*m+3*c) Cprior B0)/delta ≤ 1/t^2 := by
  let auxMoment := 3*R+3*c
  let sparseDecay := c*m+3*c
  let crudeMoment := 6*R+sparseDecay
  let auxCoefficient : ℝ≥0 := ∑ j ∈ Icc 4 q, ∑ j' ∈ Icc j q,
    sourceLocalPolynomialTailCoefficient j' auxMoment Cdegree B0
  let priorCoefficient : ℝ≥0 := ((Icc 4 q).card : ℝ≥0)+1+
    (256*(q+1 : ℝ≥0)^2)*(4*Cprior)^(crudeMoment*(2*q))*
      ((boundedIntersectionMomentCoefficient (2*q) crudeMoment : ℝ≥0)^crudeMoment+
        B0*(sourceCrudeUniformWitnessFactor q (Icc 4 q).card*(2 : ℝ≥0)^(6*q))^crudeMoment)
  obtain ⟨Tdelta, hTdelta, hdelta⟩ := eventually_polynomial_geometric_le_power 0 0 (c*m) 1 1 (by norm_num)
  obtain ⟨Tband, hTband, hband⟩ := eventually_polynomial_geometric_le_power R 3 sparseDecay
    (2*(1+(q+1 : ℝ≥0)^2)) 1 (by norm_num)
  let T := lower+Tdelta+Tband+⌈auxCoefficient⌉₊+⌈priorCoefficient⌉₊+2
  refine ⟨T, by dsimp only [T]; omega, by dsimp only [T]; omega, ?_⟩
  intro u hu t ht hscale
  dsimp only
  have hu2 : 2 ≤ u := by dsimp only [T] at hu; omega
  have huNN : (1 : ℝ≥0) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
  have hu0 : (0 : ℝ≥0) < u := zero_lt_one.trans_le huNN
  have huPower : (u : ℝ≥0) ≤ (u : ℝ≥0)^c := by
    simpa only [pow_one] using pow_le_pow_right₀ huNN hc
  have hauxCoefficient : auxCoefficient ≤ (u : ℝ≥0)^c := by
    apply le_trans _ huPower
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈auxCoefficient⌉₊ ≤ u by dsimp only [T] at hu; omega))
  have hpriorCoefficient : priorCoefficient ≤ (u : ℝ≥0)^c := by
    apply le_trans _ huPower
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈priorCoefficient⌉₊ ≤ u by dsimp only [T] at hu; omega))
  have hcm : 1 ≤ c*m := by simpa only [one_mul] using Nat.mul_le_mul hc hm
  have hdeltaSmall : 1/(u : ℝ≥0)^(c*m) < 1 := by
    have hh : 1/(u : ℝ≥0)^(c*m) ≤ 1/(u : ℝ≥0) := by
      exact inversePower_parameter_le_one_div u (c*m) huNN hcm
    exact (hh.trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ≥0) < 2)
      (by exact_mod_cast hu2))).trans_lt (by norm_num)
  have hdeltaError : (1/2 : ℝ≥0)^u ≤ 1/(u : ℝ≥0)^(c*m) := by
    simpa only [pow_zero, one_mul] using hdelta u (by dsimp only [T] at hu; omega) 0 (by simp)
  have hbandBound : ∀ n : ℕ, n ≤ u^R →
      2*((n : ℝ≥0)^2+(q+1 : ℝ≥0)^2*(n : ℝ≥0)^3)*(1/2 : ℝ≥0)^u ≤ 1/(u : ℝ≥0)^sparseDecay := by
    intro n hn
    have hn3 : (n : ℝ≥0)^3 ≤ (n+1 : ℝ≥0)^3 := by gcongr; exact le_add_of_nonneg_right zero_le
    have hn2 : (n : ℝ≥0)^2 ≤ (n+1 : ℝ≥0)^3 := by
      calc
        _ ≤ (n+1 : ℝ≥0)^2 := by gcongr; exact le_add_of_nonneg_right zero_le
        _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_left zero_le) (by norm_num : 2 ≤ 3)
    apply le_trans _ (hband u (by dsimp only [T] at hu; omega) n hn)
    calc
      _ ≤ 2*((n+1 : ℝ≥0)^3+(q+1 : ℝ≥0)^2*(n+1 : ℝ≥0)^3)*(1/2 : ℝ≥0)^u := by gcongr
      _ = _ := by ring
  exact ⟨by positivity, hdeltaSmall, cross_scale_fresh_error t u c m ht hscale, hdeltaError, hbandBound,
    cross_scale_auxiliary_degree_failure q auxMoment u c Cdegree B0 t (by omega) ht hscale hauxCoefficient,
    cross_scale_sparse_prior_failure q crudeMoment (Icc 4 q).card u c m Cprior B0
      (1/(u : ℝ≥0)^sparseDecay) t (by omega) ht hscale le_rfl hpriorCoefficient⟩

end Erdos207
