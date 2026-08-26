import ErdosProblems.Erdos486.Statement

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary analysis for Erdős Problem 486

This file records a criterion that rules out a finite limit at infinity when
two cofinal sequences force a fixed gap between function values.
-/

open Filter

namespace Erdos486

/-- A real-valued function cannot have a finite limit at `atTop` if its values
along one cofinal sequence are at least `high`, while its values along another
cofinal sequence are at most `low`, for `low < high`. -/
theorem not_tendsto_atTop_of_cofinal_ge_of_cofinal_le
    (f : ℝ → ℝ) {low high : ℝ} (hlow_high : low < high)
    (upper lower : ℕ → ℝ)
    (hupper_cofinal : Tendsto upper atTop atTop)
    (hlower_cofinal : Tendsto lower atTop atTop)
    (hupper : ∀ n, high ≤ f (upper n))
    (hlower : ∀ n, f (lower n) ≤ low) :
    ∀ d : ℝ, ¬Tendsto f atTop (nhds d) := by
  intro d hf
  have hhigh_d : high ≤ d :=
    ge_of_tendsto' (hf.comp hupper_cofinal) hupper
  have hd_low : d ≤ low :=
    le_of_tendsto' (hf.comp hlower_cofinal) hlower
  exact (not_le_of_gt hlow_high) (hhigh_d.trans hd_low)

/-- A specialization of
`not_tendsto_atTop_of_cofinal_ge_of_cofinal_le` to logarithmic averages. -/
theorem not_hasLogDensity_of_cofinal_ge_of_cofinal_le
    (B : Set ℕ) {low high : ℝ} (hlow_high : low < high)
    (upper lower : ℕ → ℝ)
    (hupper_cofinal : Tendsto upper atTop atTop)
    (hlower_cofinal : Tendsto lower atTop atTop)
    (hupper : ∀ n, high ≤ logAverage B (upper n))
    (hlower : ∀ n, logAverage B (lower n) ≤ low) :
    ∀ d : ℝ, ¬HasLogDensity B d := by
  exact not_tendsto_atTop_of_cofinal_ge_of_cofinal_le
    (logAverage B) hlow_high upper lower hupper_cofinal hlower_cofinal hupper hlower

end Erdos486
