import StackExchange.Puzzling139335.JordanRegion

/-!
# Identifying a bounded region from a Jordan curve in its frontier

A closed bounded set with connected interior and connected complement is filled
by any Jordan curve contained in its frontier, provided it is the closure of its
interior.  The proof uses the actual complementary components of that curve.
-/

open Set Schoenflies

namespace Puzzling139335.HalfTurnRemainder.JordanUnion

variable {U C : Set Plane}

/-- The connected complement of a bounded closed set lies outside every Jordan
curve contained in that set. -/
theorem compl_subset_outside_of_contains_jordan
    (hUbounded : Bornology.IsBounded U) (hUcompl : IsConnected Uᶜ)
    (hC : IsJordanCurve C) (hCU : C ⊆ U) :
    Uᶜ ⊆ outside C := by
  have hsep := jordan_curve_theorem hC
  have hcomp : Uᶜ ⊆ Cᶜ := fun _ hx hxC => hx (hCU hxC)
  intro x hx
  refine ⟨hcomp hx, ?_⟩
  intro hbounded
  have hUcBounded : Bornology.IsBounded Uᶜ :=
    hbounded.subset
      (hUcompl.isPreconnected.subset_connectedComponentIn hx hcomp)
  have huniv : Bornology.IsBounded (Set.univ : Set Plane) := by
    simpa only [union_compl_self] using hUbounded.union hUcBounded
  exact hsep.not_isBounded_outside (huniv.subset (subset_univ _))

/-- A Jordan curve in the frontier of a bounded closed set with connected
complement has all of its inside in the interior of the set. -/
theorem inside_subset_interior_of_frontier_contains_jordan
    (hUclosed : IsClosed U) (hUbounded : Bornology.IsBounded U)
    (hUcompl : IsConnected Uᶜ) (hC : IsJordanCurve C)
    (hCU : C ⊆ frontier U) : inside C ⊆ interior U := by
  have hsep := jordan_curve_theorem hC
  have hcomp := compl_subset_outside_of_contains_jordan hUbounded hUcompl hC
    (hCU.trans hUclosed.frontier_subset)
  apply hsep.isOpen_inside.subset_interior_iff.mpr
  intro x hx
  by_contra hxU
  exact Set.disjoint_left.mp disjoint_inside_outside hx (hcomp hxU)

/-- Connectedness of the interior forces the reverse inclusion as well. -/
theorem interior_eq_inside_of_frontier_contains_jordan
    (hUclosed : IsClosed U) (hUbounded : Bornology.IsBounded U)
    (hUinterior : IsConnected (interior U)) (hUcompl : IsConnected Uᶜ)
    (hC : IsJordanCurve C) (hCU : C ⊆ frontier U) :
    interior U = inside C := by
  have hsep := jordan_curve_theorem hC
  have hinside := inside_subset_interior_of_frontier_contains_jordan
    hUclosed hUbounded hUcompl hC hCU
  have hcomp : interior U ⊆ Cᶜ := by
    intro x hx hxC
    exact Set.disjoint_left.mp disjoint_interior_frontier hx (hCU hxC)
  obtain ⟨x, hx⟩ := hsep.isConnected_inside.nonempty
  have hsub := hUinterior.isPreconnected.subset_connectedComponentIn (hinside hx) hcomp
  rw [hsep.connectedComponentIn_eq_inside hx] at hsub
  exact Subset.antisymm hsub hinside

/-- The region is exactly the filling of the Jordan curve in its frontier. -/
theorem eq_closure_inside_of_frontier_contains_jordan
    (hUclosed : IsClosed U) (hUbounded : Bornology.IsBounded U)
    (hUregular : closure (interior U) = U)
    (hUinterior : IsConnected (interior U)) (hUcompl : IsConnected Uᶜ)
    (hC : IsJordanCurve C) (hCU : C ⊆ frontier U) :
    U = closure (inside C) := by
  rw [← hUregular, interior_eq_inside_of_frontier_contains_jordan
    hUclosed hUbounded hUinterior hUcompl hC hCU]

/-- In particular, the set is a Jordan region. -/
theorem isJordanRegion_of_frontier_contains_jordan
    (hUclosed : IsClosed U) (hUbounded : Bornology.IsBounded U)
    (hUregular : closure (interior U) = U)
    (hUinterior : IsConnected (interior U)) (hUcompl : IsConnected Uᶜ)
    (hC : IsJordanCurve C) (hCU : C ⊆ frontier U) :
    IsJordanRegion U :=
  ⟨C, hC, eq_closure_inside_of_frontier_contains_jordan
    hUclosed hUbounded hUregular hUinterior hUcompl hC hCU⟩

/-- No additional frontier points remain outside the given curve. -/
theorem frontier_eq_of_frontier_contains_jordan
    (hUclosed : IsClosed U) (hUbounded : Bornology.IsBounded U)
    (hUregular : closure (interior U) = U)
    (hUinterior : IsConnected (interior U)) (hUcompl : IsConnected Uᶜ)
    (hC : IsJordanCurve C) (hCU : C ⊆ frontier U) :
    frontier U = C := by
  rw [eq_closure_inside_of_frontier_contains_jordan
    hUclosed hUbounded hUregular hUinterior hUcompl hC hCU]
  exact frontier_closure_inside (jordan_curve_theorem hC)

end Puzzling139335.HalfTurnRemainder.JordanUnion
