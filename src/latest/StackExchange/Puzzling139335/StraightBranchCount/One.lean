import StackExchange.Puzzling139335.StraightBranchCount

/-!
# The unique straight branch when the intrinsic count is one

Any two straight endpoint arcs on such a boundary follow the same local
branch.  This also identifies straight branches under an actual congruence.
-/

open Set

namespace Puzzling139335.HasStraightBranchCount

theorem one_implies_sameBoundaryGerm
    {C A B : Set Plane} {v a b : Plane}
    (h : HasStraightBranchCount C v 1)
    (hA : Schoenflies.IsArcBetween A v a) (hB : Schoenflies.IsArcBetween B v b)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hAS : IsStraightAt A v) (hBS : IsStraightAt B v) : SameBoundaryGerm A B v := by
  obtain ⟨q, D, E, hcut, hn⟩ := h
  have hnotBoth : ¬ (IsStraightAt D v ∧ IsStraightAt E v) := by
    rintro ⟨hD, hE⟩
    have hD' := (straightGermIndicator_eq_one_iff D v).mpr hD
    have hE' := (straightGermIndicator_eq_one_iff E v).mpr hE
    omega
  rcases hcut.endpoint_arc_germ_eq_or hA hAC with hAD | hAE <;>
    rcases hcut.endpoint_arc_germ_eq_or hB hBC with hBD | hBE
  · exact hAD.trans hBD.symm
  · exact False.elim (hnotBoth ⟨hAS.of_sameBoundaryGerm hAD, hBS.of_sameBoundaryGerm hBE⟩)
  · exact False.elim (hnotBoth ⟨hBS.of_sameBoundaryGerm hBD, hAS.of_sameBoundaryGerm hAE⟩)
  · exact hAE.trans hBE.symm

/-- An isometry carrying one complete boundary to another identifies their
unique straight local branches. -/
theorem one_image_straight_arc_sameBoundaryGerm
    {C D A B : Set Plane} {v a w b : Plane}
    (h : HasStraightBranchCount C v 1) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (heC : e '' C = D) (hev : e v = w)
    (hA : Schoenflies.IsArcBetween A v a) (hB : Schoenflies.IsArcBetween B w b)
    (hAC : A ⊆ C) (hBD : B ⊆ D)
    (hAS : IsStraightAt A v) (hBS : IsStraightAt B w) :
    SameBoundaryGerm (e '' A) B w := by
  have hcount := h.image_affineIsometry e
  rw [heC, hev] at hcount
  have hA' := hA.image_homeomorph e.toHomeomorph
  change Schoenflies.IsArcBetween (e '' A) (e v) (e a) at hA'
  rw [hev] at hA'
  have hAS' := hAS.image_affineIsometry e
  rw [hev] at hAS'
  apply hcount.one_implies_sameBoundaryGerm hA' hB _ hBD hAS' hBS
  rw [← heC]
  exact image_mono hAC

end Puzzling139335.HasStraightBranchCount
