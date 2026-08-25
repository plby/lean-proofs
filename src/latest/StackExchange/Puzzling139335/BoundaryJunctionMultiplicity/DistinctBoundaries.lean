import StackExchange.Puzzling139335.SquareBoundaryJunctions
import StackExchange.Puzzling139335.JordanCurveRigidity

/-! # Distinct boundaries in the cover obtained by adjoining the exterior -/

open Set

namespace Puzzling139335

/-- No tile can fill the entire square, since another tile has nonempty
interior inside it. -/
theorem SquareDissection.piece_ne_unitSquare (d : SquareDissection) (i : Fin 4) :
    d.piece i ≠ unitSquare := by
  intro heq
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨x, hx⟩ := (d.jordan j).interior_nonempty
  have hxS : x ∈ interior unitSquare := interior_mono (d.piece_subset j) hx
  have hxi : x ∈ interior (d.piece i) := by simpa only [heq] using hxS
  exact Set.disjoint_left.mp (d.disjoint_interiors hji) hx hxi

/-- The four tile boundaries and the outer square boundary are all distinct.
Only the bounded tiles, not the exterior, are used as Jordan regions here. -/
theorem SquareDissection.extendedPiece_frontier_injective (d : SquareDissection) :
    Function.Injective (fun i => frontier (d.extendedPiece i)) := by
  intro i j hfront
  by_contra hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hije : i ≠ j := fun h => hij (congrArg Sum.inl h)
      have hpieces : d.piece i = d.piece j :=
        (d.jordan i).eq_of_frontier_eq (d.jordan j) hfront
      obtain ⟨x, hx⟩ := (d.jordan i).interior_nonempty
      exact Set.disjoint_left.mp (d.disjoint_interiors hije) hx (hpieces ▸ hx)
    | inr u =>
      have hfrontS : frontier (d.piece i) = frontier unitSquare := by
        simpa only [extendedPiece, frontier_closedSquareExterior] using hfront
      exact d.piece_ne_unitSquare i
        ((d.jordan i).eq_of_frontier_eq isJordanRegion_unitSquare hfrontS)
  | inr u =>
    cases j with
    | inl j =>
      have hfrontS : frontier (d.piece j) = frontier unitSquare := by
        simpa only [extendedPiece, frontier_closedSquareExterior] using hfront.symm
      exact d.piece_ne_unitSquare j
        ((d.jordan j).eq_of_frontier_eq isJordanRegion_unitSquare hfrontS)
    | inr v => exact hij (congrArg Sum.inr (Subsingleton.elim u v))

/-- A whole extended boundary cannot be included in a different one. -/
theorem SquareDissection.not_extendedPiece_frontier_subset (d : SquareDissection)
    {i j : ExtendedPieceIndex} (hij : i ≠ j) :
    ¬ frontier (d.extendedPiece i) ⊆ frontier (d.extendedPiece j) := by
  intro hsub
  apply hij
  apply d.extendedPiece_frontier_injective
  exact (d.extendedPiece_frontier_jordan i).eq_of_subset
    (d.extendedPiece_frontier_jordan j) hsub

end Puzzling139335
