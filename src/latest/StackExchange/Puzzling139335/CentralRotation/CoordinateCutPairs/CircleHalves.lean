import StackExchange.Puzzling139335.CentralRotation.CircleArcs
import Wikipedia.SchoenfliesTheorem.GeneralCrosscut

/-!
# The two halves of a circle parametrization

The two closed parameter half-intervals give actual simple arcs that cover the
circle and meet exactly at the half-period and period endpoints.
-/

open Set Schoenflies

namespace Puzzling139335.CentralRotation

/-- The zero and one parameters represent the same point of a period-one
circle, for every map from that circle. -/
theorem circleParam_zero_eq_one {X : Type*} (f : AddCircle (1 : ℝ) → X) :
    circleParam f 0 = circleParam f 1 := by
  apply congrArg f
  exact (AddCircle.coe_period (1 : ℝ)).symm

/-- The closed unit parameter interval covers the image of a circle map.
Neither continuity nor injectivity is needed for this set identity. -/
theorem circleParam_image_unitInterval {X : Type*} (f : AddCircle (1 : ℝ) → X) :
    circleParam f '' Icc (0 : ℝ) 1 = range f := by
  apply Subset.antisymm
  · rintro _ ⟨t, -, rfl⟩
    exact mem_range_self (t : AddCircle (1 : ℝ))
  · rintro _ ⟨z, rfl⟩
    let t : ℝ := AddCircle.equivIco (1 : ℝ) 0 z
    have ht : t ∈ Ico (0 : ℝ) 1 := by
      simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).property
    refine ⟨t, Ico_subset_Icc_self ht, ?_⟩
    dsimp only [circleParam, t]
    rw [AddCircle.coe_equivIco]

/-- The upper and lower parameter half-circles form a cut pair, each directed
from the half-period point to the period point. -/
theorem isCutPair_circle_halves {f : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hfc : Continuous f) (hfi : Function.Injective f) :
    IsCutPair (range f) (circleParam f (1 / 2)) (circleParam f 1)
      (circleParam f '' Icc (1 / 2 : ℝ) 1)
      (circleParam f '' Icc (0 : ℝ) (1 / 2)) := by
  have hupper := isArcBetween_circleParam hfc hfi
    (a := (1 / 2 : ℝ)) (b := 1) (by norm_num) (by norm_num)
  have hlower := isArcBetween_circleParam hfc hfi
    (a := (0 : ℝ)) (b := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨hupper, ?_, ?_, ?_⟩
  · simpa only [circleParam_zero_eq_one f] using hlower.reverse
  · rw [union_comm, ← image_union,
      Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact circleParam_image_unitInterval f
  · ext z
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
      by_cases hsone : s = 1
      · exact Or.inr (by simpa only [hsone] using
          (mem_singleton (circleParam f 1)))
      · have hslt : s < 1 := lt_of_le_of_ne hs.2 hsone
        have hst : s = t :=
          (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
            (show s ∈ Ico (0 : ℝ) (0 + 1) from ⟨by linarith [hs.1], by simpa⟩)
            (show t ∈ Ico (0 : ℝ) (0 + 1) from ⟨ht.1, by linarith [ht.2]⟩)).mp
            (hfi hts.symm)
        have hshalf : s = 1 / 2 := by linarith [hs.1, ht.2]
        exact Or.inl (congrArg (circleParam f) hshalf)
    · rintro (rfl | rfl)
      · exact ⟨⟨1 / 2, ⟨le_rfl, by norm_num⟩, rfl⟩,
          ⟨1 / 2, ⟨by norm_num, le_rfl⟩, rfl⟩⟩
      · exact ⟨⟨1, ⟨by norm_num, le_rfl⟩, rfl⟩,
          ⟨0, ⟨le_rfl, by norm_num⟩, circleParam_zero_eq_one f⟩⟩

end Puzzling139335.CentralRotation
