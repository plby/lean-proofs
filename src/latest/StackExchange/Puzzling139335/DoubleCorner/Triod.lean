import StackExchange.Puzzling139335.JordanArcGerms
import StackExchange.Puzzling139335.JordanSubarc
import Wikipedia.SchoenfliesTheorem.Polygonal

/-!
# A Jordan curve contains no triod

At a point of a Jordan curve there are only two boundary germs.  Three
nontrivial incident arcs meeting pairwise only at that point would require
three different germs.  The final theorem specializes this obstruction to
three straight segments.
-/

open Set Puzzling139335

namespace Schoenflies

/-- A Jordan curve cannot contain three endpoint arcs whose pairwise
intersections are confined to their common initial endpoint. -/
theorem IsJordanCurve.no_three_endpoint_arcs
    {C A B D : Set Plane} {v a b c : Plane}
    (hC : IsJordanCurve C)
    (hA : IsArcBetween A v a) (hB : IsArcBetween B v b)
    (hD : IsArcBetween D v c)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (hDC : D ⊆ C)
    (hAB : A ∩ B ⊆ ({v} : Set Plane))
    (hAD : A ∩ D ⊆ ({v} : Set Plane))
    (hBD : B ∩ D ⊆ ({v} : Set Plane)) : False := by
  have hAB' : A ∩ B ⊆ ({v, a} : Set Plane) := by
    intro x hx
    exact Or.inl (mem_singleton_iff.mp (hAB hx))
  have hAD' : A ∩ D ⊆ ({v, a} : Set Plane) := by
    intro x hx
    exact Or.inl (mem_singleton_iff.mp (hAD hx))
  have hBD' : B ∩ D ⊆ ({v, b} : Set Plane) := by
    intro x hx
    exact Or.inl (mem_singleton_iff.mp (hBD hx))
  obtain ⟨E, hcut⟩ := hC.exists_cutPair_of_subset_arc hA hAC
  have hnotBA : ¬ SameBoundaryGerm B A v :=
    fun h => hA.not_sameBoundaryGerm_of_inter_subset_endpoints hAB' h.symm
  have hBE : SameBoundaryGerm B E v :=
    (hcut.endpoint_arc_germ_eq_or hB hBC).resolve_left hnotBA
  rcases hcut.endpoint_arc_germ_eq_or hD hDC with hDA | hDE
  · exact hA.not_sameBoundaryGerm_of_inter_subset_endpoints hAD' hDA.symm
  · exact hB.not_sameBoundaryGerm_of_inter_subset_endpoints hBD'
      (hBE.trans hDE.symm)

/-- In particular, three nontrivial straight segments from one point, with
pairwise intersections confined to that point, cannot lie on a Jordan curve. -/
theorem IsJordanCurve.no_three_segments
    {C : Set Plane} {v a b c : Plane} (hC : IsJordanCurve C)
    (ha : a ≠ v) (hb : b ≠ v) (hc : c ≠ v)
    (hA : segment ℝ v a ⊆ C) (hB : segment ℝ v b ⊆ C)
    (hD : segment ℝ v c ⊆ C)
    (hAB : segment ℝ v a ∩ segment ℝ v b ⊆ ({v} : Set Plane))
    (hAD : segment ℝ v a ∩ segment ℝ v c ⊆ ({v} : Set Plane))
    (hBD : segment ℝ v b ∩ segment ℝ v c ⊆ ({v} : Set Plane)) : False :=
  hC.no_three_endpoint_arcs (isArcBetween_segment ha.symm)
    (isArcBetween_segment hb.symm) (isArcBetween_segment hc.symm)
    hA hB hD hAB hAD hBD

end Schoenflies
