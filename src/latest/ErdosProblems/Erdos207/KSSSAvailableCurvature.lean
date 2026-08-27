/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPoissonCurvature

/-! # Polynomial first and second derivatives of the available-triangle trajectory -/

namespace Erdos207

noncomputable section

def ksssAvailableSlope (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) : ℝ :=
  A₀ * Real.exp (-ksssPoissonExponent orders a t) *
    ((-9 / E₀) * ksssEdgeDensity E₀ t ^ 2 - ksssEdgeDensity E₀ t ^ 3 * ksssPoissonRate orders a t)

def ksssAvailableCurvature (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) : ℝ :=
  A₀ * Real.exp (-ksssPoissonExponent orders a t) *
    (54 * ksssEdgeDensity E₀ t / E₀ ^ 2 +
      18 * ksssEdgeDensity E₀ t ^ 2 * ksssPoissonRate orders a t / E₀ +
        ksssEdgeDensity E₀ t ^ 3 * ksssPoissonRate orders a t ^ 2 -
          ksssEdgeDensity E₀ t ^ 3 * ksssPoissonCurvature orders a t)

theorem hasDerivAt_ksssAvailableTrajectory_slope
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) :
    HasDerivAt (ksssAvailableTrajectory orders a E₀ A₀) (ksssAvailableSlope orders a E₀ A₀ t) t := by
  have h := (((hasDerivAt_ksssEdgeDensity E₀ t).pow 3).const_mul A₀).mul
    ((hasDerivAt_ksssPoissonExponent orders a t).neg.exp)
  convert! h using 1
  dsimp only [ksssAvailableSlope, Pi.pow_apply, Pi.neg_apply]
  ring

theorem hasDerivAt_ksssAvailableSlope
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) (hE : E₀ ≠ 0) :
    HasDerivAt (ksssAvailableSlope orders a E₀ A₀) (ksssAvailableCurvature orders a E₀ A₀ t) t := by
  have hp := hasDerivAt_ksssEdgeDensity E₀ t
  have hr := hasDerivAt_ksssPoissonRate orders a t
  have he := (hasDerivAt_ksssPoissonExponent orders a t).neg.exp
  have h := (he.const_mul A₀).mul
    (((hp.pow 2).const_mul (-9 / E₀)).sub ((hp.pow 3).mul hr))
  convert! h using 1
  dsimp only [ksssAvailableCurvature, Pi.pow_apply, Pi.neg_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp <;> ring

theorem ksssAvailableSlope_eq_neg_threat
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d) (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0) :
    ksssAvailableSlope orders a E₀ A₀ t = -ksssThreatTrajectory orders a E₀ A₀ t :=
  (hasDerivAt_ksssAvailableTrajectory_slope orders a E₀ A₀ t).unique
    (hasDerivAt_ksssAvailableTrajectory orders a E₀ A₀ t horders hE hp)

end

end Erdos207
