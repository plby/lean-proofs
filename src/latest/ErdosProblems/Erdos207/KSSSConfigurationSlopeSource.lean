/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationCurvature

/-! # Identification of the polynomial configuration slopes with the drift equations -/

namespace Erdos207

noncomputable section

theorem ksssConfigurationSlope_zero_source
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d)
    (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0)
    (hA : ksssAvailableTrajectory orders a E₀ A₀ t ≠ 0)
    {d : ℕ} (hd : 1 ≤ d) :
    ksssConfigurationSlope orders a E₀ A₀ d 0 t =
      -(d : ℝ) * ksssConfigurationTrajectory orders a E₀ A₀ d 0 t *
        ksssThreatTrajectory orders a E₀ A₀ t / ksssAvailableTrajectory orders a E₀ A₀ t :=
  (hasDerivAt_ksssConfigurationTrajectory_slope orders a E₀ A₀ d 0 t).unique
    (hasDerivAt_ksssConfigurationTrajectory_zero orders a E₀ A₀ t horders hE hp hA hd)

theorem ksssConfigurationSlope_succ_source
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d)
    (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0)
    (hA : ksssAvailableTrajectory orders a E₀ A₀ t ≠ 0)
    {d c : ℕ} (hcd : c + 1 < d) :
    ksssConfigurationSlope orders a E₀ A₀ d (c + 1) t =
      (((d - c : ℕ) : ℝ) * ksssConfigurationTrajectory orders a E₀ A₀ d c t -
        ((d - (c + 1) : ℕ) : ℝ) * ksssConfigurationTrajectory orders a E₀ A₀ d (c + 1) t *
          ksssThreatTrajectory orders a E₀ A₀ t) / ksssAvailableTrajectory orders a E₀ A₀ t :=
  (hasDerivAt_ksssConfigurationTrajectory_slope orders a E₀ A₀ d (c + 1) t).unique
    (hasDerivAt_ksssConfigurationTrajectory_succ orders a E₀ A₀ t horders hE hp hA hcd)

end

end Erdos207
