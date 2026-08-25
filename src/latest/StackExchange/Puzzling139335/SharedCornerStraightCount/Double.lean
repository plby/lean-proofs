import StackExchange.Puzzling139335.SharedCornerStraightCount
import StackExchange.Puzzling139335.StraightBranchCount.One

/-!
# The one- or two-straight-branch alternatives at a repeated double corner

At least one tile branch is straight because the two exterior straight
branches are paired with tile branches.  Congruence then excludes an
intrinsic straight-branch count of zero for two copies of one point.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.SquareDissection

theorem common_straightBranchCount_pos_of_two_owners
    (d : SquareDissection) (j : Fin 4) {i k : Fin 4} {n : ℕ}
    (hik : i ≠ k) (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hcommon : ∀ l : Fin 4, corner j ∈ d.piece l →
      HasStraightBranchCount (frontier (d.piece l)) (corner j) n) : 0 < n := by
  classical
  have hjJ := d.corner_mem_tripleContactSet_of_two_pieces hik hi hk
  obtain ⟨F, hTwo, _⟩ := d.exists_exact_boundary_arc_family
  have hext := F.card_exterior_straightOccurrences_corner hTwo j hjJ
  have hpos := F.tile_straight_count_pos_of_exterior_card_two (corner j) hext
  by_contra hn
  have hn0 : n = 0 := by omega
  have hzero : (∑ l : Fin 4, (F.straightBoundaryOccurrences (.inl l) (corner j)).card) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : corner j ∈ d.piece l
    · have hcard := F.card_straightBoundaryOccurrences_eq hTwo (.inl l)
        ⟨d.corner_mem_frontier hl, hjJ⟩ (hcommon l hl)
      exact hcard.trans hn0
    · have hnot : corner j ∉ frontier (d.extendedPiece (.inl l)) := by
        change corner j ∉ frontier (d.piece l)
        rwa [d.corner_mem_frontier_iff l j]
      rw [F.straightBoundaryOccurrences_eq_empty_of_not_mem_frontier (.inl l) hnot]
      rfl
  omega

/-- The two copies of one point at a double corner have either one or two
straight branches.  Zero is ruled out by the actual paired interfaces. -/
theorem hasStraightBranchCount_one_or_two_of_two_equal_intrinsic
    (d : SquareDissection) (j : Fin 4) (a : Plane)
    (htwo : d.cornerTileCount j = 2)
    (htype : ∀ i : Fin 4, corner j ∈ d.piece i → d.intrinsicCorner i j = a) :
    HasStraightBranchCount (frontier (d.piece 0)) a 1 ∨
      HasStraightBranchCount (frontier (d.piece 0)) a 2 := by
  classical
  let owners : Finset (Fin 4) := Finset.univ.filter (fun i => corner j ∈ d.piece i)
  have howners : owners.card = 2 := htwo
  obtain ⟨i, hi, k, hk, hik⟩ := Finset.one_lt_card.mp (show 1 < owners.card by omega)
  have hiPiece : corner j ∈ d.piece i := (Finset.mem_filter.mp hi).2
  have hkPiece : corner j ∈ d.piece k := (Finset.mem_filter.mp hk).2
  have ha : a ∈ frontier (d.piece 0) :=
    htype i hiPiece ▸ d.intrinsicCorner_mem_frontier hiPiece
  obtain ⟨n, hn⟩ := exists_straightBranchCount (d.jordan 0).frontier_isJordanCurve ha
  have hcommon (l : Fin 4) (hl : corner j ∈ d.piece l) :
      HasStraightBranchCount (frontier (d.piece l)) (corner j) n := by
    apply d.straightBranchCount_at_corner_of_intrinsic l j
    rwa [htype l hl]
  have hpos := d.common_straightBranchCount_pos_of_two_owners j hik hiPiece hkPiece hcommon
  have hle := hn.le_two
  have hn12 : n = 1 ∨ n = 2 := by omega
  rcases hn12 with rfl | rfl
  · exact Or.inl hn
  · exact Or.inr hn

end Puzzling139335.SquareDissection
