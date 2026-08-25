import StackExchange.Puzzling139335.N6.TripleTypes
import StackExchange.Puzzling139335.SharedCornerStraightCount
import StackExchange.Puzzling139335.GeometricReduction

/-!
# Actual straight boundary branches at a triple corner

All reductions are discharged here from a putative six-incidence
counterexample: the rectangular-hull theorem gives at most three types,
the unique-corner argument gives one shared type, and paired boundary
interfaces force that type to have two straight initial branches.
-/

open Set

namespace Puzzling139335.N6

/-- The prototype point used by any owner of the triple corner has two
straight boundary branches, without a type-count or angle hypothesis. -/
theorem intrinsic_straightBranchCount_two_at_triple (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    {s i : Fin 4} (hs : d.cornerTileCount s = 3) (hi : corner s ∈ d.piece i) :
    HasStraightBranchCount (frontier (d.piece 0)) (d.intrinsicCorner i s) 2 := by
  apply d.hasStraightBranchCount_two_of_three_equal_intrinsic s
    (d.intrinsicCorner i s) hs
  intro j hj
  exact intrinsicCorners_eq_at_triple d hc hN
    (d.usedCornerTypes_card_le_three hc) hs hj hi

/-- Each of the three physical tile boundaries has two straight branches
at the common square corner. -/
theorem straightBranchCount_two_at_triple (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    {s i : Fin 4} (hs : d.cornerTileCount s = 3) (hi : corner s ∈ d.piece i) :
    HasStraightBranchCount (frontier (d.piece i)) (corner s) 2 :=
  d.straightBranchCount_at_corner_of_intrinsic i s
    (intrinsic_straightBranchCount_two_at_triple d hc hN hs hi)

/-- The actual local boundary is a union of two nondegenerate straight
segments with no common point except the square corner. -/
theorem exists_two_segments_at_triple (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    {s i : Fin 4} (hs : d.cornerTileCount s = 3) (hi : corner s ∈ d.piece i) :
    ∃ b c : Plane, b ≠ corner s ∧ c ≠ corner s ∧
      segment ℝ (corner s) b ⊆ frontier (d.piece i) ∧
      segment ℝ (corner s) c ⊆ frontier (d.piece i) ∧
      segment ℝ (corner s) b ∩ segment ℝ (corner s) c = {corner s} ∧
      SameBoundaryGerm (frontier (d.piece i))
        (segment ℝ (corner s) b ∪ segment ℝ (corner s) c) (corner s) :=
  (straightBranchCount_two_at_triple d hc hN hs hi).exists_two_segments

end Puzzling139335.N6
