import StackExchange.Puzzling139335.BoundaryJunctionMultiplicity.DistinctBoundaries
import StackExchange.Puzzling139335.BoundaryJunctionMultiplicity.PuncturedCurve
import StackExchange.Puzzling139335.FiniteBoundaryPartition.ClosedCover
import Wikipedia.SchoenfliesTheorem.FreshDenseSelection

/-!
# Every extended boundary has at least two triple junctions

Deleting at most one point leaves a Jordan curve connected.  A finite closed
partner cover must therefore have one constant partner there.  Density then
puts the entire Jordan boundary into the partner boundary, contradicting the
distinctness of the five boundaries.
-/

open Set

namespace Puzzling139335

/-- Each tile boundary, and also the square boundary viewed from the
exterior, contains at least two distinct triple junctions. -/
theorem SquareDissection.extendedBoundaryJunctions_nontrivial (d : SquareDissection)
    (i : ExtendedPieceIndex) :
    (frontier (d.extendedPiece i) ∩ tripleContactSet d.extendedPiece).Nontrivial := by
  classical
  apply Set.not_subsingleton_iff.mp
  intro hsmall
  let C := frontier (d.extendedPiece i)
  let E := tripleContactSet d.extendedPiece
  have hC : Schoenflies.IsJordanCurve C := d.extendedPiece_frontier_jordan i
  have hdiff : C \ E = C \ (C ∩ E) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hconn : IsConnected (C \ E) := by
    rw [hdiff]
    exact hC.isConnected_sdiff_subsingleton hsmall
  let J := {j : ExtendedPieceIndex // j ≠ i}
  let T : J → Set Plane := fun j => frontier (d.extendedPiece j.val)
  have hclosed (j : J) : IsClosed (T j) := isClosed_frontier
  have hcover : C \ E ⊆ ⋃ j : J, T j := by
    intro x hx
    have hxi : x ∈ d.extendedPiece i := (d.extendedPiece_closed i).closure_eq ▸ hx.1.1
    obtain ⟨j, hji, hxj⟩ := boundary_mem_another_of_closed_cover d.extendedPiece
      d.extendedPiece_closed d.extendedPiece_covers hx.1
    have hxjf : x ∈ frontier (d.extendedPiece j) := by
      apply (mem_frontier_iff_notMem_interior hxj).mpr
      intro hint
      exact Set.disjoint_left.mp
        (disjoint_interior_piece_of_regular d.extendedPiece d.extendedPiece_regular
          d.extendedPiece_disjoint_interiors hji) hint hxi
    exact mem_iUnion.mpr ⟨⟨j, hji⟩, hxjf⟩
  have hdis : Pairwise fun j k : J =>
      Disjoint ((C \ E) ∩ T j) ((C \ E) ∩ T k) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro x hxj hxk
    apply hxj.1.2
    refine ⟨i, j.val, k.val, j.property.symm, k.property.symm,
      (fun h => hjk (Subtype.ext h)), ?_, ?_, ?_⟩
    · exact (d.extendedPiece_closed i).closure_eq ▸ hxj.1.1.1
    · exact (d.extendedPiece_closed j.val).closure_eq ▸ hxj.2.1
    · exact (d.extendedPiece_closed k.val).closure_eq ▸ hxk.2.1
  obtain ⟨j, hj⟩ := exists_subset_of_finite_closed_cover hconn hclosed hcover hdis
  apply d.not_extendedPiece_frontier_subset j.property.symm
  exact (hC.subset_closure_sdiff_finite subset_rfl subset_closure
    d.extendedTripleContactSet_finite).trans (closure_minimal hj (hclosed j))

/-- Extended cardinality formulation of the two-junction lower bound. -/
theorem SquareDissection.two_le_extendedBoundaryJunctions_encard (d : SquareDissection)
    (i : ExtendedPieceIndex) :
    2 ≤ (frontier (d.extendedPiece i) ∩ tripleContactSet d.extendedPiece).encard := by
  simpa only [one_add_one_eq_two] using
    (ENat.add_one_le_iff ENat.one_ne_top).mpr
      (one_lt_encard_iff_nontrivial.mpr (d.extendedBoundaryJunctions_nontrivial i))

end Puzzling139335
