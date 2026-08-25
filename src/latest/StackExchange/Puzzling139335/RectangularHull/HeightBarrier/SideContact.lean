import StackExchange.Puzzling139335.JordanCrosscut

/-! # A boundary contact determines the side of a crosscut -/

open Set Schoenflies

namespace Puzzling139335.RectangularHull

/-- A connected set avoiding a crosscut lies on the side approached by any
contact strictly within one of the two boundary arcs. -/
theorem subset_crosscut_side_of_boundary_contact {C X A B Q : Set Plane}
    {p q r : Plane} (hX : JordanCrosscut C X p q) (hcut : IsCutPair C p q A B)
    (hQ : IsPreconnected Q) (hQS : Q ⊆ inside C) (hQX : Disjoint Q X)
    (hr : r ∈ closure Q) (hrA : r ∈ A) (hrB : r ∉ B) :
    Q ⊆ inside (A ∪ X) := by
  have hsub : Q ⊆ inside C \ X := by
    intro z hz
    exact ⟨hQS hz, fun hzX => Set.disjoint_left.mp hQX hz hzX⟩
  have hcover : Q ⊆ inside (A ∪ X) ∪ inside (B ∪ X) :=
    hX.inside_diff_eq hcut ▸ hsub
  have hopenA := (jordan_curve_theorem (hX.isJordanCurve_union hcut)).isOpen_inside
  have hopenB := (jordan_curve_theorem (hX.isJordanCurve_union hcut.symm)).isOpen_inside
  rcases hQ.subset_or_subset hopenA hopenB (hX.disjoint_sides hcut) hcover with hA | hB
  · exact hA
  · have hr' : r ∈ closure (inside (B ∪ X)) ∩ C :=
      ⟨closure_mono hB hr, hcut.fst_subset hrA⟩
    rw [hX.closure_side_inter hcut.symm] at hr'
    exact False.elim (hrB hr')

end Puzzling139335.RectangularHull
