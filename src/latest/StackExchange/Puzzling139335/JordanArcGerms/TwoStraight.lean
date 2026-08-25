import StackExchange.Puzzling139335.JordanArcGerms

/-!
# Two straight boundary branches

Two distinct straight endpoint branches on a Jordan curve exhaust its local
branches.  Every other endpoint arc therefore contains a straight initial
segment as well.
-/

open Set Puzzling139335

namespace Schoenflies

/-- Two straight arcs representing distinct branches force every incident
endpoint arc on the same Jordan curve to be straight at the common endpoint. -/
theorem IsJordanCurve.endpoint_arc_isStraightAt_of_two_straight
    {C A B D : Set Plane} {v a b w : Plane}
    (hC : IsJordanCurve C) (hA : IsArcBetween A v a) (hB : IsArcBetween B v b)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (hinter : A ∩ B ⊆ ({v, a} : Set Plane))
    (hstraightA : Puzzling139335.IsStraightAt A v)
    (hstraightB : Puzzling139335.IsStraightAt B v)
    (hD : IsArcBetween D v w) (hDC : D ⊆ C) : Puzzling139335.IsStraightAt D v := by
  obtain ⟨A', hcut⟩ := hC.exists_cutPair_of_subset_arc hA hAC
  have hnot : ¬ SameBoundaryGerm B A v :=
    fun h => hA.not_sameBoundaryGerm_of_inter_subset_endpoints hinter h.symm
  have hBA' : SameBoundaryGerm B A' v :=
    (hcut.endpoint_arc_germ_eq_or hB hBC).resolve_left hnot
  have hstraightA' : Puzzling139335.IsStraightAt A' v :=
    hstraightB.of_sameBoundaryGerm hBA'
  rcases hcut.endpoint_arc_germ_eq_or hD hDC with hDA | hDA'
  · exact hstraightA.of_sameBoundaryGerm hDA.symm
  · exact hstraightA'.of_sameBoundaryGerm hDA'.symm

end Schoenflies
