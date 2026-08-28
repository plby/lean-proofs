import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneCutoff
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOneBasic

/-!
# Actual closed-form primitives on each compact disc–annulus region

The coefficient germs are extended separately across the deleted axis by
an inner cutoff. The actual two Cauchy–Green integrals then solve both
equations on the prescribed closed region, using closedness only there.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

open PeriodTorusLineBundleClassification

theorem exists_smooth_primitive_on_annularClosed {f g : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (hg : ContDiffOn ℝ ∞ g domain)
    (hclosed : ∀ q ∈ domain, dbarFirst g q = dbarSecond f q)
    (R : ℝ) (hR : 0 < R) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧
      ∀ q ∈ annularClosed R, dbarFirst u q = f q ∧ dbarSecond u q = g q := by
  obtain ⟨v, hv, hev⟩ := exists_smooth_representative_away_zero hf R⁻¹ (inv_pos.mpr hR)
  obtain ⟨w, hw, hew⟩ := exists_smooth_representative_away_zero hg R⁻¹ (inv_pos.mpr hR)
  obtain ⟨χ, hχ, hcχ, hχone⟩ := exists_complex_cutoff R hR
  have hcl : ∀ z t, χ z ≠ 0 → t ∈ closedBall (0 : ℂ) R \ ball 0 R⁻¹ →
      dbarFirst w (z, t) = dbarSecond v (z, t) := by
    intro z t _ ht
    have hlo : R⁻¹ ≤ ‖t‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using ht.2
    rw [DbarLocalOne.dbarFirst_eq_of_eventuallyEq (hew (z, t) hlo),
      DbarLocalOne.dbarSecond_eq_of_eventuallyEq (hev (z, t) hlo)]
    exact hclosed (z, t) (Laurent.closedAnnulus_subset_punctured (inv_pos.mpr hR) ht)
  refine ⟨localDbarPrimitive χ χ v w,
    contDiff_localDbarPrimitive hχ hχ hcχ hcχ hv hw, ?_⟩
  intro q hq
  have hlo : R⁻¹ ≤ ‖q.2‖ := by
    simpa only [mem_ball, dist_zero_right, not_lt] using hq.2.2
  constructor
  · exact (dbarFirst_localDbarPrimitive hχ hχ hcχ hcχ hv hw q (hχone q.1 hq.1)).trans
      (hev q hlo).eq_of_nhds
  · exact (DbarLocalOne.dbarSecond_localDbarPrimitive_of_closedOn hχ hχ hcχ hcχ hv hw
      hcl (fun t ht => hχone t ht.1) q hq.2).trans (hew q hlo).eq_of_nhds

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
