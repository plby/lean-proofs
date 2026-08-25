import StackExchange.Puzzling139335.Definitions
import Wikipedia.SchoenfliesTheorem.JordanClosed

/-!
# Elementary topology of the Jordan pieces

The existing Jordan-curve theorem identifies the bounded complementary region
and its frontier.  The results below expose the corresponding facts for the
closed pieces used by `SquareDissection`.  No additional axiom is introduced.
-/

open Set

namespace Puzzling139335

/-- The bounded component of a Jordan complement is regular open. -/
theorem interior_closure_inside {C : Set Plane} (hC : Schoenflies.IsSeparating C) :
    interior (closure (Schoenflies.inside C)) = Schoenflies.inside C := by
  have hdis : Disjoint (closure (Schoenflies.inside C)) (Schoenflies.outside C) :=
    Schoenflies.disjoint_inside_outside.closure_left hC.isOpen_outside
  have hdis' : Disjoint (interior (closure (Schoenflies.inside C)))
      (closure (Schoenflies.outside C)) :=
    (hdis.mono_left interior_subset).closure_right isOpen_interior
  apply Subset.antisymm ?_ hC.isOpen_inside.subset_interior_closure
  intro x hx
  have hxcl := interior_subset hx
  rw [(Schoenflies.IsRegionOf.inside C).closure_eq hC] at hxcl
  rcases hxcl with hxI | hxC
  · exact hxI
  · exact False.elim (Set.disjoint_left.mp hdis' hx
      ((Schoenflies.IsRegionOf.outside C).subset_closure hC hxC))

/-- Filling a Jordan curve does not change its frontier. -/
theorem frontier_closure_inside {C : Set Plane} (hC : Schoenflies.IsSeparating C) :
    frontier (closure (Schoenflies.inside C)) = C := by
  rw [frontier, closure_closure, interior_closure_inside hC]
  simpa only [frontier, hC.isOpen_inside.interior_eq] using hC.frontier_inside

namespace IsJordanRegion

variable {P Q : Set Plane}

theorem isClosed (hP : IsJordanRegion P) : IsClosed P := by
  obtain ⟨C, _, rfl⟩ := hP
  exact isClosed_closure

theorem isCompact (hP : IsJordanRegion P) : IsCompact P := by
  obtain ⟨C, hC, rfl⟩ := hP
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (Schoenflies.jordan_curve_theorem hC).isBounded_inside.closure

theorem isBounded (hP : IsJordanRegion P) : Bornology.IsBounded P :=
  hP.isCompact.isBounded

theorem isConnected_interior (hP : IsJordanRegion P) : IsConnected (interior P) := by
  obtain ⟨C, hC, rfl⟩ := hP
  have hsep := Schoenflies.jordan_curve_theorem hC
  rw [interior_closure_inside hsep]
  exact hsep.isConnected_inside

theorem interior_nonempty (hP : IsJordanRegion P) : (interior P).Nonempty :=
  hP.isConnected_interior.nonempty

theorem nonempty (hP : IsJordanRegion P) : P.Nonempty :=
  hP.interior_nonempty.mono interior_subset

/-- Every point of a piece is a limit of interior points. -/
theorem closure_interior (hP : IsJordanRegion P) : closure (interior P) = P := by
  obtain ⟨C, hC, rfl⟩ := hP
  rw [interior_closure_inside (Schoenflies.jordan_curve_theorem hC)]

theorem isConnected (hP : IsJordanRegion P) : IsConnected P := by
  rw [← hP.closure_interior]
  exact hP.isConnected_interior.closure

theorem frontier_isJordanCurve (hP : IsJordanRegion P) :
    Schoenflies.IsJordanCurve (frontier P) := by
  obtain ⟨C, hC, rfl⟩ := hP
  rw [frontier_closure_inside (Schoenflies.jordan_curve_theorem hC)]
  exact hC

theorem frontier_nonempty (hP : IsJordanRegion P) : (frontier P).Nonempty :=
  hP.frontier_isJordanCurve.nonempty

/-- Disjoint interiors also exclude the closed other piece from an interior. -/
theorem disjoint_interior_left (hQ : IsJordanRegion Q)
    (h : Disjoint (interior P) (interior Q)) : Disjoint (interior P) Q := by
  rw [← hQ.closure_interior]
  exact h.closure_right isOpen_interior

end IsJordanRegion

theorem SquareDissection.disjoint_interior_piece (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (interior (d.piece i)) (d.piece j) :=
  (d.jordan j).disjoint_interior_left (d.disjoint_interiors hij)

theorem SquareDissection.not_mem_other_piece (d : SquareDissection)
    {i j : Fin 4} {p : Plane} (hij : i ≠ j) (hp : p ∈ interior (d.piece i)) :
    p ∉ d.piece j :=
  fun hq => Set.disjoint_left.mp (d.disjoint_interior_piece hij) hp hq

end Puzzling139335
