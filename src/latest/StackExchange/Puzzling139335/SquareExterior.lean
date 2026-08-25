import StackExchange.Puzzling139335.ExteriorContact.Square
import StackExchange.Puzzling139335.WeightedMass.Square
import StackExchange.Puzzling139335.BoundaryPartners

/-!
# Adjoining the exterior of the square

The fifth region is the unbounded closed exterior, not a closed Jordan disk.
It is closed and regular closed, and adjoining it turns a square dissection
into a finite cover of the whole plane with disjoint interiors.
-/

open Set

namespace Puzzling139335

theorem closure_interior_unitSquare : closure (interior unitSquare) = unitSquare := by
  have hC := Schoenflies.jordan_curve_theorem isJordanCurve_frontier_unitSquare
  rw [← inside_frontier_unitSquare, (Schoenflies.IsRegionOf.inside _).closure_eq hC,
    inside_frontier_unitSquare, ← closure_eq_interior_union_frontier,
    isClosed_unitSquare.closure_eq]

theorem isJordanRegion_unitSquare : IsJordanRegion unitSquare :=
  ⟨frontier unitSquare, isJordanCurve_frontier_unitSquare, by
    rw [inside_frontier_unitSquare, closure_interior_unitSquare]⟩

/-- The closed, unbounded fifth region. -/
def closedSquareExterior : Set Plane := closure unitSquareᶜ

theorem isClosed_closedSquareExterior : IsClosed closedSquareExterior := isClosed_closure

theorem interior_closedSquareExterior : interior closedSquareExterior = unitSquareᶜ := by
  rw [closedSquareExterior, closure_compl, interior_compl, closure_interior_unitSquare]

theorem closure_interior_closedSquareExterior :
    closure (interior closedSquareExterior) = closedSquareExterior := by
  rw [interior_closedSquareExterior]
  rfl

theorem unitSquare_inter_closedSquareExterior :
    unitSquare ∩ closedSquareExterior = frontier unitSquare := by
  rw [closedSquareExterior, closure_compl, isClosed_unitSquare.frontier_eq]
  rfl

theorem frontier_closedSquareExterior : frontier closedSquareExterior = frontier unitSquare := by
  rw [isClosed_closedSquareExterior.frontier_eq, interior_closedSquareExterior,
    closedSquareExterior, closure_compl, isClosed_unitSquare.frontier_eq]
  ext x
  simp only [mem_sdiff, mem_compl_iff]
  tauto

/-- Four bounded pieces and the single unbounded exterior region. -/
abbrev ExtendedPieceIndex := Fin 4 ⊕ Unit

def SquareDissection.extendedPiece (d : SquareDissection) : ExtendedPieceIndex → Set Plane
  | .inl i => d.piece i
  | .inr _ => closedSquareExterior

@[simp] theorem SquareDissection.extendedPiece_tile (d : SquareDissection) (i : Fin 4) :
    d.extendedPiece (.inl i) = d.piece i := rfl

@[simp] theorem SquareDissection.extendedPiece_exterior (d : SquareDissection) :
    d.extendedPiece (.inr ()) = closedSquareExterior := rfl

theorem SquareDissection.extendedPiece_closed (d : SquareDissection) (i : ExtendedPieceIndex) :
    IsClosed (d.extendedPiece i) := by
  cases i with
  | inl i => exact (d.jordan i).isClosed
  | inr u => exact isClosed_closedSquareExterior

theorem SquareDissection.extendedPiece_regular (d : SquareDissection) (i : ExtendedPieceIndex) :
    closure (interior (d.extendedPiece i)) = d.extendedPiece i := by
  cases i with
  | inl i => exact (d.jordan i).closure_interior
  | inr u => exact closure_interior_closedSquareExterior

theorem SquareDissection.extendedPiece_covers (d : SquareDissection) :
    (⋃ i, d.extendedPiece i) = univ := by
  apply Subset.antisymm (subset_univ _)
  intro x _
  by_cases hx : x ∈ unitSquare
  · obtain ⟨i, hi⟩ := d.exists_piece_mem hx
    exact mem_iUnion.mpr ⟨.inl i, hi⟩
  · exact mem_iUnion.mpr ⟨.inr (), subset_closure hx⟩

theorem SquareDissection.extendedPiece_disjoint_interiors (d : SquareDissection) :
    Pairwise fun i j => Disjoint (interior (d.extendedPiece i))
      (interior (d.extendedPiece j)) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => exact d.disjoint_interiors (fun h => hij (congrArg Sum.inl h))
    | inr u =>
      change Disjoint (interior (d.piece i)) (interior closedSquareExterior)
      rw [interior_closedSquareExterior]
      exact Set.disjoint_left.mpr fun x hx hout => hout (d.piece_subset i (interior_subset hx))
  | inr u =>
    cases j with
    | inl j =>
      change Disjoint (interior closedSquareExterior) (interior (d.piece j))
      rw [interior_closedSquareExterior]
      exact Set.disjoint_left.mpr fun x hout hx => hout (d.piece_subset j (interior_subset hx))
    | inr v => exact False.elim (hij (congrArg Sum.inr (Subsingleton.elim u v)))

/-- Off the extended triple-junction set, every tile boundary has one local
partner, including the possibility that the partner is the exterior. -/
theorem SquareDissection.extendedPiece_boundary_partner (d : SquareDissection)
    {i : ExtendedPieceIndex} {x : Plane} (hx : x ∈ frontier (d.extendedPiece i))
    (hnot : x ∉ tripleContactSet d.extendedPiece) :
    ∃ j, j ≠ i ∧ ∃ r > 0,
      Metric.ball x r ⊆ d.extendedPiece i ∪ d.extendedPiece j ∧
      Metric.ball x r ∩ frontier (d.extendedPiece i) =
        Metric.ball x r ∩ frontier (d.extendedPiece j) ∧
      ∀ k, k ≠ i → k ≠ j → Disjoint (Metric.ball x r) (d.extendedPiece k) :=
  boundary_partner_neighborhood d.extendedPiece d.extendedPiece_closed
    d.extendedPiece_regular d.extendedPiece_disjoint_interiors d.extendedPiece_covers hx hnot

end Puzzling139335
