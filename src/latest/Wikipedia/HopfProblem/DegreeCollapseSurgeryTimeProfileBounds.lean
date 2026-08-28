import Wikipedia.HopfProblem.DegreeCollapseSurgeryTimeProfile

/-!
# Small time sublevels are unchanged by the original surgery profile

The profile is a convex combination of the old time and one. A threshold
below both half the attachment margin and one therefore has exactly the
same strict sublevel and symmetric time band before and after profiling.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryTimeProfile

theorem le_profile_of_le (δ t c : ℝ) (hct : c ≤ t) (hc1 : c ≤ 1) : c ≤ profile δ t := by
  have hw0 : 0 ≤ weight δ t := Real.smoothTransition.nonneg _
  have hw1 : weight δ t ≤ 1 := Real.smoothTransition.le_one _
  have hfirst := mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hct)
  have hsecond := mul_nonneg hw0 (sub_nonneg.mpr hc1)
  dsimp [profile]
  nlinarith

theorem profile_lt_small_iff {δ ε : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ / 2) (hε1 : ε ≤ 1)
    (t : ℝ) : profile δ t < ε ↔ t < ε := by
  constructor
  · intro hp
    by_contra ht
    exact (not_lt_of_ge (le_profile_of_le δ t ε (le_of_not_gt ht) hε1)) hp
  · intro ht
    rw [profile_eq_self hδ (ht.le.trans hε)]
    exact ht

theorem profile_mem_small_band_iff {δ ε : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ / 2) (hε1 : ε ≤ 1)
    (t : ℝ) : profile δ t ∈ Ioo (-ε) ε ↔ t ∈ Ioo (-ε) ε := by
  constructor
  · intro ht
    have hu := (profile_lt_small_iff hδ hε hε1 t).1 ht.2
    rw [profile_eq_self hδ (hu.le.trans hε)] at ht
    exact ht
  · intro ht
    rw [profile_eq_self hδ (ht.2.le.trans hε)]
    exact ht

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryTimeProfile
