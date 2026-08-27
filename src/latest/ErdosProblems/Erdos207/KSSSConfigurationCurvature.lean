/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerProductCurvature
import ErdosProblems.Erdos207.KSSSAvailableCurvature
import ErdosProblems.Erdos207.UnitStepTaylor

/-! # Configuration-trajectory curvature, including the zero-time endpoint -/

namespace Erdos207

noncomputable section

def ksssConfigurationSlope (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (d c : ℕ) (t : ℝ) : ℝ :=
  (d.choose c : ℝ) * a d * powerProductSlope c (d - c)
    (ksssAvailableTrajectory orders a E₀ A₀) (ksssAvailableSlope orders a E₀ A₀) t

def ksssConfigurationCurvature (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (d c : ℕ) (t : ℝ) : ℝ :=
  (d.choose c : ℝ) * a d * powerProductCurvature c (d - c)
    (ksssAvailableTrajectory orders a E₀ A₀) (ksssAvailableSlope orders a E₀ A₀)
    (ksssAvailableCurvature orders a E₀ A₀) t

theorem hasDerivAt_ksssConfigurationTrajectory_slope
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (d c : ℕ) (t : ℝ) :
    HasDerivAt (ksssConfigurationTrajectory orders a E₀ A₀ d c)
      (ksssConfigurationSlope orders a E₀ A₀ d c t) t := by
  have h := (hasDerivAt_powerProduct c (d - c)
    (ksssAvailableTrajectory orders a E₀ A₀) (ksssAvailableSlope orders a E₀ A₀) t
    (hasDerivAt_ksssAvailableTrajectory_slope orders a E₀ A₀ t)).const_mul ((d.choose c : ℝ) * a d)
  convert! h using 1
  funext u
  dsimp only [ksssConfigurationTrajectory]
  ring

theorem hasDerivAt_ksssConfigurationSlope
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (d c : ℕ) (t : ℝ) (hE : E₀ ≠ 0) :
    HasDerivAt (ksssConfigurationSlope orders a E₀ A₀ d c)
      (ksssConfigurationCurvature orders a E₀ A₀ d c t) t := by
  exact (hasDerivAt_powerProductSlope c (d - c)
    (ksssAvailableTrajectory orders a E₀ A₀) (ksssAvailableSlope orders a E₀ A₀)
    (ksssAvailableCurvature orders a E₀ A₀) t
    (hasDerivAt_ksssAvailableTrajectory_slope orders a E₀ A₀ t)
    (hasDerivAt_ksssAvailableSlope orders a E₀ A₀ t hE)).const_mul ((d.choose c : ℝ) * a d)

theorem ksssConfigurationTrajectory_unitStep_error_le
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (d c : ℕ) (t C : ℝ)
    (hE : E₀ ≠ 0) (hC : 0 ≤ C)
    (hcurv : ∀ u ∈ Set.Icc t (t + 1), |ksssConfigurationCurvature orders a E₀ A₀ d c u| ≤ C) :
    |ksssConfigurationTrajectory orders a E₀ A₀ d c (t + 1) -
      ksssConfigurationTrajectory orders a E₀ A₀ d c t -
        ksssConfigurationSlope orders a E₀ A₀ d c t| ≤ C := by
  exact unitStep_taylor_error_le _ _ _ t C hC
    (fun u _ ↦ hasDerivAt_ksssConfigurationTrajectory_slope orders a E₀ A₀ d c u)
    (fun u _ ↦ hasDerivAt_ksssConfigurationSlope orders a E₀ A₀ d c u hE) hcurv

end

end Erdos207
