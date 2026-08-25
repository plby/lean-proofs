import StackExchange.Puzzling139335.InterfaceStraightCount
import StackExchange.Puzzling139335.SquareCornerGerms
import StackExchange.Puzzling139335.IntrinsicCorners
import StackExchange.Puzzling139335.StraightBranchCount.TwoRays

/-!
# Equal straight-branch counts at shared square corners

The exterior contributes two straight branches.  Each internal interface
contributes twice to the tile count.  Consequently three incident copies
of one intrinsic boundary point must each have two straight branches.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.SquareDissection

/-- Three tile boundaries with the same intrinsic straight-branch count at
one square corner necessarily each have two straight branches. -/
theorem common_straightBranchCount_eq_two_of_three_owners
    (d : SquareDissection) (j : Fin 4) {n : ℕ}
    (hthree : d.cornerTileCount j = 3)
    (hcommon : ∀ i : Fin 4, corner j ∈ d.piece i →
      HasStraightBranchCount (frontier (d.piece i)) (corner j) n) : n = 2 := by
  classical
  let owners : Finset (Fin 4) := Finset.univ.filter (fun i => corner j ∈ d.piece i)
  have howners : owners.card = 3 := hthree
  obtain ⟨i, hi, k, hk, hik⟩ := Finset.one_lt_card.mp (show 1 < owners.card by omega)
  have hiPiece : corner j ∈ d.piece i := (Finset.mem_filter.mp hi).2
  have hkPiece : corner j ∈ d.piece k := (Finset.mem_filter.mp hk).2
  have hjJ : corner j ∈ tripleContactSet d.extendedPiece :=
    d.corner_mem_tripleContactSet_of_two_pieces hik hiPiece hkPiece
  obtain ⟨F, hTwo, _⟩ := d.exists_exact_boundary_arc_family
  have hext := F.card_exterior_straightOccurrences_corner hTwo j hjJ
  have hcard (l : Fin 4) : (F.straightBoundaryOccurrences (.inl l) (corner j)).card =
      if corner j ∈ d.piece l then n else 0 := by
    by_cases hl : corner j ∈ d.piece l
    · rw [if_pos hl]
      exact F.card_straightBoundaryOccurrences_eq hTwo (.inl l)
        ⟨d.corner_mem_frontier hl, hjJ⟩ (hcommon l hl)
    · rw [if_neg hl]
      have hnot : corner j ∉ frontier (d.extendedPiece (.inl l)) := by
        change corner j ∉ frontier (d.piece l)
        rwa [d.corner_mem_frontier_iff l j]
      rw [F.straightBoundaryOccurrences_eq_empty_of_not_mem_frontier (.inl l) hnot]
      rfl
  have hsum : (∑ l : Fin 4, (F.straightBoundaryOccurrences (.inl l) (corner j)).card) =
      3 * n := by
    calc
      (∑ l : Fin 4, (F.straightBoundaryOccurrences (.inl l) (corner j)).card) =
          ∑ l : Fin 4, if corner j ∈ d.piece l then n else 0 :=
        Finset.sum_congr rfl (fun l _ => hcard l)
      _ = ∑ _l ∈ owners, n := by simp only [owners, Finset.sum_filter]
      _ = owners.card * n := by simp
      _ = 3 * n := by rw [howners]
  have heven := F.even_tile_straight_count_of_exterior_card_two (corner j) hext
  have hpos := F.tile_straight_count_pos_of_exterior_card_two (corner j) hext
  rw [hsum] at heven hpos
  have hle := (hcommon i hiPiece).le_two
  obtain ⟨m, hm⟩ := heven
  omega

/-- Chosen placements transport the actual frontier of the prototype. -/
theorem placement_image_frontier (d : SquareDissection) (i : Fin 4) :
    d.placement i '' frontier (d.piece 0) = frontier (d.piece i) := by
  have h := (d.placement i).toHomeomorph.image_frontier (d.piece 0)
  change d.placement i '' frontier (d.piece 0) =
    frontier (d.placement i '' d.piece 0) at h
  rwa [d.placement_image] at h

/-- The intrinsic point used at an occupied corner is on the prototype
boundary, not merely in the closed prototype. -/
theorem intrinsicCorner_mem_frontier (d : SquareDissection) {i j : Fin 4}
    (hi : corner j ∈ d.piece i) : d.intrinsicCorner i j ∈ frontier (d.piece 0) := by
  have hj := d.corner_mem_frontier hi
  rw [← d.placement_image_frontier i] at hj
  obtain ⟨p, hp, heq⟩ := hj
  have hpEq : p = d.intrinsicCorner i j := by
    apply (d.placement i).injective
    exact heq.trans (d.placement_intrinsicCorner i j).symm
  exact hpEq ▸ hp

/-- The straight-branch count at an intrinsic corner transfers to its
physical occurrence in any chosen placement. -/
theorem straightBranchCount_at_corner_of_intrinsic
    (d : SquareDissection) (i j : Fin 4) {n : ℕ}
    (h : HasStraightBranchCount (frontier (d.piece 0)) (d.intrinsicCorner i j) n) :
    HasStraightBranchCount (frontier (d.piece i)) (corner j) n := by
  have h' := h.image_affineIsometry (d.placement i)
  rwa [d.placement_image_frontier, d.placement_intrinsicCorner] at h'

/-- Three incident congruent copies of one intrinsic boundary point force
that point to have two genuine straight initial branches. -/
theorem hasStraightBranchCount_two_of_three_equal_intrinsic
    (d : SquareDissection) (j : Fin 4) (a : Plane)
    (hthree : d.cornerTileCount j = 3)
    (htype : ∀ i : Fin 4, corner j ∈ d.piece i → d.intrinsicCorner i j = a) :
    HasStraightBranchCount (frontier (d.piece 0)) a 2 := by
  obtain ⟨i, hi⟩ := d.incidence_covers j
  have hiPiece : corner j ∈ d.piece i := hi
  have ha : a ∈ frontier (d.piece 0) :=
    htype i hiPiece ▸ d.intrinsicCorner_mem_frontier hiPiece
  obtain ⟨n, hn⟩ := exists_straightBranchCount (d.jordan 0).frontier_isJordanCurve ha
  have hnTwo : n = 2 := d.common_straightBranchCount_eq_two_of_three_owners j hthree (by
    intro l hl
    apply d.straightBranchCount_at_corner_of_intrinsic l j
    rwa [htype l hl])
  exact hnTwo ▸ hn

/-- The actual local two-ray certificate at the prototype point shared by
three copies at one square corner. -/
theorem exists_two_segments_of_three_equal_intrinsic
    (d : SquareDissection) (j : Fin 4) (a : Plane)
    (hthree : d.cornerTileCount j = 3)
    (htype : ∀ i : Fin 4, corner j ∈ d.piece i → d.intrinsicCorner i j = a) :
    ∃ b c : Plane, b ≠ a ∧ c ≠ a ∧
      segment ℝ a b ⊆ frontier (d.piece 0) ∧
      segment ℝ a c ⊆ frontier (d.piece 0) ∧
      segment ℝ a b ∩ segment ℝ a c = {a} ∧
      SameBoundaryGerm (frontier (d.piece 0)) (segment ℝ a b ∪ segment ℝ a c) a :=
  (d.hasStraightBranchCount_two_of_three_equal_intrinsic j a hthree htype).exists_two_segments

end Puzzling139335.SquareDissection
