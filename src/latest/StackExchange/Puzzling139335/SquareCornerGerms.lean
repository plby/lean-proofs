import StackExchange.Puzzling139335.JordanArcGerms.TwoStraight
import StackExchange.Puzzling139335.SquareCornerGerms.Sides
import StackExchange.Puzzling139335.InterfaceParity
import StackExchange.Puzzling139335.CornerIncidence

/-!
# Straight exterior branches at square corners

The two square sides meeting at a corner represent its two boundary branches.
Every endpoint arc on the square boundary is therefore straight there.  At a
shared corner, which is an actual junction vertex of the exact partitions,
the exterior contributes exactly two straight arc occurrences.
-/

open Set
open scoped BigOperators

namespace Puzzling139335

/-- Any endpoint arc on the square boundary starts with a straight segment
when its initial endpoint is a square corner. -/
theorem square_corner_endpoint_arc_isStraightAt (c : Fin 4)
    {A : Set Plane} {w : Plane}
    (hA : Schoenflies.IsArcBetween A (corner c) w)
    (hsub : A ⊆ frontier unitSquare) : IsStraightAt A (corner c) := by
  obtain ⟨a, b, ha, hb, hsa, hsb, hinter⟩ := square_corner_two_straight_segments c
  have hmeet : segment ℝ (corner c) a ∩ segment ℝ (corner c) b ⊆
      ({corner c, a} : Set Plane) := by
    rw [hinter]
    exact singleton_subset_iff.mpr (Or.inl rfl)
  exact isJordanCurve_frontier_unitSquare.endpoint_arc_isStraightAt_of_two_straight
    (Schoenflies.isArcBetween_segment ha.symm) (Schoenflies.isArcBetween_segment hb.symm)
    hsa hsb hmeet ⟨a, ha, subset_rfl⟩ ⟨b, hb, subset_rfl⟩ hA hsub

/-- Either named endpoint of a square-boundary arc is a straight branch if
that endpoint is a square corner. -/
theorem square_corner_arc_endpoint_isStraightAt (c : Fin 4)
    {A : Set Plane} {a b : Plane} (hA : Schoenflies.IsArcBetween A a b)
    (hsub : A ⊆ frontier unitSquare) (hend : corner c = a ∨ corner c = b) :
    IsStraightAt A (corner c) := by
  rcases hend with ha | hb
  · have hA' : Schoenflies.IsArcBetween A (corner c) b := by
      simpa only [ha] using hA
    exact square_corner_endpoint_arc_isStraightAt c hA' hsub
  · have hA' : Schoenflies.IsArcBetween A (corner c) a := by
      simpa only [hb] using hA.reverse
    exact square_corner_endpoint_arc_isStraightAt c hA' hsub

/-- Every square corner belongs to the closed exterior region. -/
theorem corner_mem_closedSquareExterior (c : Fin 4) : corner c ∈ closedSquareExterior := by
  have hfront := corner_mem_frontier_of_subset (subset_refl unitSquare) (corner_mem_unitSquare c)
  rw [← unitSquare_inter_closedSquareExterior] at hfront
  exact hfront.2

/-- Two distinct tile owners, together with the exterior, make a shared
square corner a triple junction of the extended family. -/
theorem SquareDissection.corner_mem_tripleContactSet_of_two_pieces (d : SquareDissection)
    {i j c : Fin 4} (hij : i ≠ j)
    (hi : corner c ∈ d.piece i) (hj : corner c ∈ d.piece j) :
    corner c ∈ tripleContactSet d.extendedPiece := by
  refine ⟨.inl i, .inl j, .inr (), ?_, by simp, by simp,
    hi, hj, corner_mem_closedSquareExterior c⟩
  exact fun h => hij (Sum.inl.inj h)

namespace ExactBoundaryArcFamily

variable {d : SquareDissection} (F : ExactBoundaryArcFamily d)

/-- At a shared square corner, the straight exterior occurrences are
precisely the exterior arcs incident to the corner as an endpoint. -/
theorem exterior_isStraightAt_iff_endpoint (c : Fin 4)
    (hvJ : corner c ∈ tripleContactSet d.extendedPiece)
    (k : Fin (F.n (.inr ()))) :
    IsStraightAt (F.arc (.inr ()) k) (corner c) ↔
      corner c = F.left (.inr ()) k ∨ corner c = F.right (.inr ()) k := by
  constructor
  · intro hstraight
    by_contra hnot
    exact Set.disjoint_left.mp (F.arcInterior_disjoint (.inr ()) k)
      ⟨hstraight.mem, hnot⟩ hvJ
  · intro hend
    have hsub : F.arc (.inr ()) k ⊆ frontier unitSquare := by
      intro x hx
      have hfront := (F.subset_frontiers (.inr ()) k hx).1
      change x ∈ frontier closedSquareExterior at hfront
      rwa [frontier_closedSquareExterior] at hfront
    exact square_corner_arc_endpoint_isStraightAt c (F.arc_between (.inr ()) k) hsub hend

/-- The exterior has exactly two straight occurrences at every square corner
which belongs to the junction set. -/
theorem card_exterior_straightOccurrences_corner (hF : F.HasTwoGerms) (c : Fin 4)
    (hvJ : corner c ∈ tripleContactSet d.extendedPiece) :
    (F.straightBoundaryOccurrences (.inr ()) (corner c)).card = 2 := by
  classical
  have hvfront : corner c ∈ frontier (d.extendedPiece (.inr ())) := by
    change corner c ∈ frontier closedSquareExterior
    rw [frontier_closedSquareExterior]
    exact corner_mem_frontier_of_subset (subset_refl unitSquare) (corner_mem_unitSquare c)
  have hdegree := hF (.inr ()) (corner c) ⟨hvfront, hvJ⟩
  have hset : (F.straightBoundaryOccurrences (.inr ()) (corner c) :
      Set (Fin (F.n (.inr ())))) =
      {k | corner c = F.left (.inr ()) k ∨ corner c = F.right (.inr ()) k} := by
    ext k
    exact F.mem_straightBoundaryOccurrences.trans (F.exterior_isStraightAt_iff_endpoint c hvJ k)
  rw [← hset, encard_coe_eq_coe_finsetCard] at hdegree
  exact_mod_cast hdegree

/-- After removing the two exterior branches, the straight occurrences on
the four tiles at a shared square corner have even total cardinality. -/
theorem even_tile_straight_count_at_shared_corner (hF : F.HasTwoGerms) (c : Fin 4)
    (hvJ : corner c ∈ tripleContactSet d.extendedPiece) :
    Even (∑ i : Fin 4, (F.straightBoundaryOccurrences (.inl i) (corner c)).card) :=
  F.even_tile_straight_count_of_exterior_card_two (corner c)
    (F.card_exterior_straightOccurrences_corner hF c hvJ)

end ExactBoundaryArcFamily

end Puzzling139335
