import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspBall

/-!
# Shrinking cusp-coordinate radii

The exponential radius of a horodisc is strictly decreasing with its height
and tends to zero.  Thus arbitrarily small cusp-coordinate balls can be
chosen above any prescribed height and above the cusp width.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem cuspRadius_strictAnti : StrictAnti cuspRadius := by
  intro Y Z hYZ
  change Real.exp (-2 * Real.pi * Z / width) < Real.exp (-2 * Real.pi * Y / width)
  apply Real.exp_lt_exp.mpr
  apply div_lt_div_of_pos_right _ width_pos
  exact mul_lt_mul_of_neg_left hYZ (by nlinarith [Real.pi_pos])

theorem cuspRadius_antitone : Antitone cuspRadius := cuspRadius_strictAnti.antitone

theorem cuspRadius_tendsto_zero : Tendsto cuspRadius atTop (𝓝 0) := by
  have hneg : -2 * Real.pi < 0 := by nlinarith [Real.pi_pos]
  exact Real.tendsto_exp_atBot.comp
    ((tendsto_id.const_mul_atTop_of_neg hneg).atBot_div_const width_pos)

/-- A sufficiently high horodisc has arbitrarily small cusp radius. -/
theorem exists_high_cuspRadius_lt (Y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : ℝ, Y ≤ Z ∧ width ≤ Z ∧ cuspRadius Z < ε := by
  have hsmall : ∀ᶠ Z in atTop, cuspRadius Z < ε :=
    cuspRadius_tendsto_zero.eventually (gt_mem_nhds hε)
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp hsmall
  refine ⟨max Y (max width Z), le_max_left _ _, ?_, hZ _ ?_⟩
  · exact (le_max_left width Z).trans (le_max_right Y _)
  · exact (le_max_right width Z).trans (le_max_right Y _)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
