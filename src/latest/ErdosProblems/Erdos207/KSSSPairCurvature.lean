/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSSourceNormalization
import ErdosProblems.Erdos207.KSSSPoissonCurvature

/-! # Exact first and second derivatives of the pair trajectory -/

namespace Erdos207

noncomputable section

theorem ksssPairTrajectory_source_all
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) :
    ksssPairTrajectory orders a E₀ A₀ t =
      (3 * A₀ / E₀) * ksssEdgeDensity E₀ t ^ 2 * Real.exp (-ksssPoissonExponent orders a t) := by
  by_cases hE : E₀ = 0
  · simp [hE, ksssPairTrajectory]
  by_cases hp : ksssEdgeDensity E₀ t = 0
  · simp [hp, ksssPairTrajectory]
  rw [ksssPairTrajectory_source orders a E₀ A₀ t hE hp]
  ring

def ksssPairSlope (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) : ℝ :=
  (3 * A₀ / E₀) * Real.exp (-ksssPoissonExponent orders a t) *
    ((-6 / E₀) * ksssEdgeDensity E₀ t - ksssEdgeDensity E₀ t ^ 2 * ksssPoissonRate orders a t)

def ksssPairCurvature (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) : ℝ :=
  (3 * A₀ / E₀) * Real.exp (-ksssPoissonExponent orders a t) *
    (18 / E₀ ^ 2 + 12 * ksssEdgeDensity E₀ t * ksssPoissonRate orders a t / E₀ +
      ksssEdgeDensity E₀ t ^ 2 * ksssPoissonRate orders a t ^ 2 -
        ksssEdgeDensity E₀ t ^ 2 * ksssPoissonCurvature orders a t)

theorem hasDerivAt_ksssPairTrajectory_slope
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) :
    HasDerivAt (ksssPairTrajectory orders a E₀ A₀) (ksssPairSlope orders a E₀ A₀ t) t := by
  have h := (((hasDerivAt_ksssEdgeDensity E₀ t).pow 2).mul
    ((hasDerivAt_ksssPoissonExponent orders a t).neg.exp)).const_mul (3 * A₀ / E₀)
  convert! h using 1
  · funext u
    rw [ksssPairTrajectory_source_all]
    dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply]
    ring
  · dsimp only [ksssPairSlope, Pi.pow_apply, Pi.neg_apply]
    ring

theorem hasDerivAt_ksssPairSlope
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) (hE : E₀ ≠ 0) :
    HasDerivAt (ksssPairSlope orders a E₀ A₀) (ksssPairCurvature orders a E₀ A₀ t) t := by
  have hp := hasDerivAt_ksssEdgeDensity E₀ t
  have hr := hasDerivAt_ksssPoissonRate orders a t
  have he := (hasDerivAt_ksssPoissonExponent orders a t).neg.exp
  have h := (he.const_mul (3 * A₀ / E₀)).mul
    ((hp.const_mul (-6 / E₀)).sub ((hp.pow 2).mul hr))
  convert! h using 1
  dsimp only [ksssPairCurvature, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

end

end Erdos207
