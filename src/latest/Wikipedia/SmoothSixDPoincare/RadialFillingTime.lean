import Wikipedia.SmoothSixDPoincare.Hemisphere
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Radial time in a collared cylinder

The time coordinate is the projection of `1 - ‖v‖` to the closed interval.
It is smooth in the open annulus. The endpoint collars will remove its
nonsmoothness at the origin and at the unit sphere in the actual filling.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.RadialFilling

variable {n : ℕ}

/-- Radial time, running from the contracted end at the center to the original map at radius one. -/
def radialTime (v : Hemisphere.Ambient (n + 1)) : unitInterval :=
  projIcc 0 1 zero_le_one (1 - ‖v‖)

theorem coe_radialTime (v : Hemisphere.Ambient (n + 1)) :
    (radialTime v : ℝ) = max 0 (min 1 (1 - ‖v‖)) := rfl

/-- The outer radial collar maps into the original-map endpoint collar. -/
theorem radialTime_le_quarter {v : Hemisphere.Ambient (n + 1)} (hv : 3 / 4 ≤ ‖v‖) :
    (radialTime v : ℝ) ≤ 1 / 4 := by
  rw [coe_radialTime]
  exact max_le (by norm_num) ((min_le_right _ _).trans (by linarith))

/-- A whole neighborhood of the center maps into the constant endpoint collar. -/
theorem three_quarters_le_radialTime {v : Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) :
    3 / 4 ≤ (radialTime v : ℝ) := by
  rw [coe_radialTime]
  exact le_max_of_le_right (le_min (by norm_num) (by linarith))

/-- In the open annulus the radial time is smooth for the native interval manifold structure. -/
theorem contMDiffAt_radialTime {v : Hemisphere.Ambient (n + 1)}
    (hv : 0 < ‖v‖) (hunit : ‖v‖ < 1) :
    ContMDiffAt 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡∂ 1) ∞ radialTime v := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (projIcc (0 : ℝ) 1 zero_le_one) (Icc 0 1) :=
    contMDiffOn_projIcc
  have hm : 1 - ‖v‖ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hn : Icc (0 : ℝ) 1 ∈ 𝓝 (1 - ‖v‖) := Icc_mem_nhds (by linarith) (by linarith)
  have hproj := (hp _ hm).contMDiffAt hn
  have hnorm : ContDiffAt ℝ ∞ (norm : Hemisphere.Ambient (n + 1) → ℝ) v :=
    contDiffAt_norm ℝ (norm_pos_iff.mp hv)
  exact hproj.comp v (contDiffAt_const.sub hnorm).contMDiffAt

end Wikipedia.SmoothSixDPoincare.RadialFilling
