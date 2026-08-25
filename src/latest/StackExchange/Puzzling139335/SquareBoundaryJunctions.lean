import StackExchange.Puzzling139335.SquareExterior
import StackExchange.Puzzling139335.ExteriorContact
import StackExchange.Puzzling139335.TripleContact

/-!
# Finite junctions after adjoining the square exterior

Three bounded pieces have finitely many common points by the Jordan `K₃,₃`
argument.  Two bounded pieces and the exterior have finitely many common
points by the exterior-spoke version of the same argument.
-/

open Set

namespace Puzzling139335

theorem tripleContactSet_finite_of_intersections {ι : Type*} [Finite ι]
    (P : ι → Set Plane)
    (hfinite : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → (P i ∩ P j ∩ P k).Finite) :
    (tripleContactSet P).Finite := by
  classical
  let T := {q : ι × ι × ι // q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2}
  have hf (q : T) : (P q.val.1 ∩ P q.val.2.1 ∩ P q.val.2.2).Finite :=
    hfinite _ _ _ q.property.1 q.property.2.1 q.property.2.2
  apply (Set.finite_iUnion hf).subset
  rintro x ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩
  exact mem_iUnion.mpr ⟨⟨(i, j, k), hij, hik, hjk⟩, ⟨⟨hi, hj⟩, hk⟩⟩

theorem SquareDissection.pair_closedSquareExterior_finite (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) :
    (d.piece i ∩ d.piece j ∩ closedSquareExterior).Finite := by
  apply (d.pair_frontier_unitSquare_finite hij).subset
  rintro x ⟨⟨hi, hj⟩, hext⟩
  refine ⟨⟨hi, hj⟩, ?_⟩
  rw [← unitSquare_inter_closedSquareExterior]
  exact ⟨d.piece_subset i hi, hext⟩

/-- The junction set for the whole-plane cover, including exterior contacts,
is finite. -/
theorem SquareDissection.extendedTripleContactSet_finite (d : SquareDissection) :
    (tripleContactSet d.extendedPiece).Finite := by
  apply tripleContactSet_finite_of_intersections
  intro i j k hij hik hjk
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      cases k with
      | inl k =>
        exact jordan_regions_triple_intersection_finite_of_distinct d.piece d.jordan
          d.disjoint_interiors (fun h => hij (congrArg Sum.inl h))
          (fun h => hik (congrArg Sum.inl h)) (fun h => hjk (congrArg Sum.inl h))
      | inr u =>
        exact d.pair_closedSquareExterior_finite (fun h => hij (congrArg Sum.inl h))
    | inr u =>
      cases k with
      | inl k =>
        have hf := d.pair_closedSquareExterior_finite (fun h => hik (congrArg Sum.inl h))
        apply hf.subset
        rintro x ⟨⟨hi, hext⟩, hk⟩
        exact ⟨⟨hi, hk⟩, hext⟩
      | inr v => exact False.elim (hjk (congrArg Sum.inr (Subsingleton.elim u v)))
  | inr u =>
    cases j with
    | inl j =>
      cases k with
      | inl k =>
        have hf := d.pair_closedSquareExterior_finite (fun h => hjk (congrArg Sum.inl h))
        apply hf.subset
        rintro x ⟨⟨hext, hj⟩, hk⟩
        exact ⟨⟨hj, hk⟩, hext⟩
      | inr v => exact False.elim (hik (congrArg Sum.inr (Subsingleton.elim u v)))
    | inr v => exact False.elim (hij (congrArg Sum.inr (Subsingleton.elim u v)))

theorem SquareDissection.extendedPiece_frontier_jordan (d : SquareDissection)
    (i : ExtendedPieceIndex) : Schoenflies.IsJordanCurve (frontier (d.extendedPiece i)) := by
  cases i with
  | inl i => exact (d.jordan i).frontier_isJordanCurve
  | inr u =>
    change Schoenflies.IsJordanCurve (frontier closedSquareExterior)
    rw [frontier_closedSquareExterior]
    exact isJordanCurve_frontier_unitSquare

end Puzzling139335
