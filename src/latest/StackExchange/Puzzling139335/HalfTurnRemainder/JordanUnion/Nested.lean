import StackExchange.Puzzling139335.JordanCrosscut
import StackExchange.Puzzling139335.JordanAccessibility

/-!
# Crosscuts and a connected remainder

If a closed set contains a crosscut of a Jordan disk and its remainder in the
open disk is connected, one of the two boundary arcs belongs to that set.
This is the separation step used to recover a connected contact set.
-/

open Set Schoenflies

namespace Puzzling139335.HalfTurnRemainder

/-- A connected remainder cannot occupy both sides of a crosscut contained
in the removed closed set.  One complete outer boundary arc is removed. -/
theorem outer_arc_subset_of_connected_remainder
    {C P D M N : Set Plane} {p q : Plane}
    (hX : JordanCrosscut C P p q) (hcut : IsCutPair C p q M N)
    (hD : IsClosed D) (hPD : P ⊆ D)
    (hconn : IsPreconnected (inside C \ D)) :
    M ⊆ D ∨ N ⊆ D := by
  have hcover : inside C \ D ⊆ inside (M ∪ P) ∪ inside (N ∪ P) := by
    rw [← hX.inside_diff_eq hcut]
    intro x hx
    exact ⟨hx.1, fun hxP => hx.2 (hPD hxP)⟩
  have hM := jordan_curve_theorem (hX.isJordanCurve_union hcut)
  have hN := jordan_curve_theorem (hX.isJordanCurve_union hcut.symm)
  rcases hconn.subset_or_subset hM.isOpen_inside hN.isOpen_inside
      (hX.disjoint_sides hcut) hcover with hleft | hright
  · right
    have hfill : inside (N ∪ P) ⊆ D := by
      intro x hx
      by_contra hxD
      exact Set.disjoint_left.mp (hX.disjoint_sides hcut)
        (hleft ⟨(hX.side_subset hcut.symm hx).1, hxD⟩) hx
    have hclosed := closure_minimal hfill hD
    intro x hx
    have hx' : x ∈ closure (inside (N ∪ P)) ∩ C := by
      rw [hX.closure_side_inter hcut.symm]
      exact hx
    exact hclosed hx'.1
  · left
    have hfill : inside (M ∪ P) ⊆ D := by
      intro x hx
      by_contra hxD
      exact Set.disjoint_left.mp (hX.disjoint_sides hcut) hx
        (hright ⟨(hX.side_subset hcut hx).1, hxD⟩)
    have hclosed := closure_minimal hfill hD
    intro x hx
    have hx' : x ∈ closure (inside (M ∪ P)) ∩ C := by
      rw [hX.closure_side_inter hcut]
      exact hx
    exact hclosed hx'.1

/-- Two different frontier points of a Jordan region are joined by an arc
whose other points are in the interior.  Two disjoint access spokes give
the arc, so no local boundary smoothness is assumed. -/
theorem exists_arc_between_frontier_through_interior
    {D : Set Plane} {p q : Plane} (hD : IsJordanRegion D)
    (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hpq : p ≠ q) :
    ∃ P : Set Plane, IsArcBetween P p q ∧
      P \ {p, q} ⊆ interior D ∧ P ⊆ D := by
  obtain ⟨z, hz⟩ := hD.interior_nonempty
  let b : Bool → Plane := fun i => if i then p else q
  have hb : ∀ i, b i ∈ frontier D := by
    intro i
    cases i
    · exact hq
    · exact hp
  have hbi : Function.Injective b := by
    intro i j hij
    cases i <;> cases j <;> simp_all [b]
  obtain ⟨A, harc, hinside, hmeet⟩ :=
    hD.exists_disjoint_arcs_to_frontier hz b hb hbi
  have hleft : IsArcBetween (A true) z p := by simpa [b] using harc true
  have hright : IsArcBetween (A false) z q := by simpa [b] using harc false
  have hP : IsArcBetween (A true ∪ A false) p q := by
    apply hleft.reverse.concatenate hright
    intro x hx hy
    exact mem_singleton_iff.mp (hmeet true false (by decide) ▸ ⟨hx, hy⟩)
  have hopen : (A true ∪ A false) \ {p, q} ⊆ interior D := by
    intro x hx
    rcases hx.1 with hxleft | hxright
    · apply hinside true
      refine ⟨hxleft, ?_⟩
      simpa [b] using fun hxp : x = p => hx.2 (Or.inl hxp)
    · apply hinside false
      refine ⟨hxright, ?_⟩
      simpa [b] using fun hxq : x = q => hx.2 (Or.inr hxq)
  refine ⟨A true ∪ A false, hP, hopen, ?_⟩
  intro x hx
  by_cases hend : x ∈ ({p, q} : Set Plane)
  · rcases hend with rfl | rfl
    · exact hD.isClosed.closure_eq ▸ hp.1
    · exact hD.isClosed.closure_eq ▸ hq.1
  · exact interior_subset (hopen ⟨hx, hend⟩)

end Puzzling139335.HalfTurnRemainder
