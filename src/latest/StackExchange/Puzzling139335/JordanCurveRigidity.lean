import StackExchange.Puzzling139335.JordanRegion

/-!
# Inclusion rigidity of Jordan boundaries

A Jordan curve cannot be a proper subset of another Jordan curve.  The
proof uses the two complementary regions and their common frontier.
-/

open Set Schoenflies

namespace Schoenflies

theorem IsJordanCurve.eq_of_subset {C D : Set Plane} (hC : IsJordanCurve C)
    (hD : IsJordanCurve D) (hCD : C ⊆ D) : C = D := by
  have hCs := jordan_curve_theorem hC
  have hDs := jordan_curve_theorem hD
  have hout : outside D ⊆ outside C := by
    intro x hx
    have hsub : outside D ⊆ Cᶜ := fun y hy hyC => hy.1 (hCD hyC)
    refine ⟨hsub hx, ?_⟩
    intro hb
    apply hDs.not_isBounded_outside
    exact hb.subset (hDs.isConnected_outside.isPreconnected.subset_connectedComponentIn hx hsub)
  have hpD : IsRegionPair D (inside D) (outside D) := Or.inl ⟨rfl, rfl⟩
  have hpC : IsRegionPair C (outside C) (inside C) := Or.inr ⟨rfl, rfl⟩
  have hsub := cell_subset_region_diff (P := (∅ : Set Plane))
    hDs hCs hpD hpC hout (empty_subset C)
  obtain ⟨x, hx⟩ := hCs.isConnected_inside.nonempty
  have hcomp := cell_isComponent (P := (∅ : Set Plane)) hDs hCs hpD hpC hout
    (empty_subset C) (by simpa only [union_empty] using hCD) x hx
  rw [sdiff_empty] at hcomp
  have hinside : inside C = inside D := hcomp.symm.trans
    (hDs.isConnected_inside.isPreconnected.connectedComponentIn (hsub hx).1)
  rw [← hCs.frontier_inside, ← hDs.frontier_inside, hinside]

end Schoenflies

namespace Puzzling139335.IsJordanRegion

theorem interior_eq_inside_frontier {P : Set Plane} (hP : IsJordanRegion P) :
    interior P = inside (frontier P) := by
  obtain ⟨C, hC, rfl⟩ := hP
  have hCs := jordan_curve_theorem hC
  rw [interior_closure_inside hCs, frontier_closure_inside hCs]

theorem eq_of_frontier_eq {P Q : Set Plane} (hP : IsJordanRegion P)
    (hQ : IsJordanRegion Q) (hfront : frontier P = frontier Q) : P = Q := by
  rw [← hP.closure_interior, ← hQ.closure_interior,
    hP.interior_eq_inside_frontier, hQ.interior_eq_inside_frontier, hfront]

theorem eq_of_frontier_subset {P Q : Set Plane} (hP : IsJordanRegion P)
    (hQ : IsJordanRegion Q) (hfront : frontier P ⊆ frontier Q) : P = Q :=
  hP.eq_of_frontier_eq hQ (hP.frontier_isJordanCurve.eq_of_subset hQ.frontier_isJordanCurve hfront)

end Puzzling139335.IsJordanRegion
