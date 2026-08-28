import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneCutoff
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOneBasic

/-!
# Actual closed-form primitives on products of compact annuli

The globally smooth representatives preserve coefficient germs on the
two annuli. An annular first cutoff ensures that every nonzero integrand
uses the original closedness equation, even though the representatives
are not asserted to be globally closed.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

open PeriodTorusLineBundleClassification

theorem exists_smooth_primitive_on_annularClosed {f g : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (hg : ContDiffOn ℝ ∞ g domain)
    (hclosed : ∀ q ∈ domain, dbarFirst g q = dbarSecond f q)
    (R : ℝ) (hR : 0 < R) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧
      ∀ q ∈ annularClosed R, dbarFirst u q = f q ∧ dbarSecond u q = g q := by
  obtain ⟨v, hv, hev⟩ := exists_smooth_representative_away_axes hf (R⁻¹ / 2) (by positivity)
  obtain ⟨w, hw, hew⟩ := exists_smooth_representative_away_axes hg (R⁻¹ / 2) (by positivity)
  obtain ⟨χ₁, hχ₁, hcχ₁, hχ₁one, hχ₁away⟩ := exists_annular_cutoff R hR
  obtain ⟨χ₂, hχ₂, hcχ₂, hχ₂one⟩ := exists_complex_cutoff R hR
  have hlo (z : ℂ) (hz : z ∈ closedAnnulus R) : R⁻¹ / 2 ≤ ‖z‖ := by
    have hi : R⁻¹ ≤ ‖z‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hz.2
    have hp := inv_pos.mpr hR
    linarith
  have hcl : ∀ z t, χ₁ z ≠ 0 → t ∈ closedAnnulus R →
      dbarFirst w (z, t) = dbarSecond v (z, t) := by
    intro z t hz ht
    have hzlo := (hχ₁away z hz).le
    have htlo := hlo t ht
    rw [DbarLocalOne.dbarFirst_eq_of_eventuallyEq (hew (z, t) hzlo htlo),
      DbarLocalOne.dbarSecond_eq_of_eventuallyEq (hev (z, t) hzlo htlo)]
    have hzne : z ≠ 0 := norm_pos_iff.mp ((by positivity : 0 < R⁻¹ / 2).trans_le hzlo)
    exact hclosed (z, t) ⟨hzne, closedAnnulus_subset_punctured hR ht⟩
  refine ⟨localDbarPrimitive χ₁ χ₂ v w,
    contDiff_localDbarPrimitive hχ₁ hχ₂ hcχ₁ hcχ₂ hv hw, ?_⟩
  intro q hq
  constructor
  · exact (dbarFirst_localDbarPrimitive hχ₁ hχ₂ hcχ₁ hcχ₂ hv hw q
      (hχ₁one q.1 hq.1)).trans (hev q (hlo q.1 hq.1) (hlo q.2 hq.2)).eq_of_nhds
  · exact (DbarLocalOne.dbarSecond_localDbarPrimitive_of_closedOn hχ₁ hχ₂ hcχ₁ hcχ₂ hv hw
      hcl (fun t ht => hχ₂one t ht.1) q hq.2).trans
      (hew q (hlo q.1 hq.1) (hlo q.2 hq.2)).eq_of_nhds

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
