import StackExchange.Puzzling139335.N6.Triple
import StackExchange.Puzzling139335.ReflectionSeparation

/-!
# The remaining actual corner owners after full-pair normalization

Transporting a genuine full corner fixes the two unique physical
corners. The six-incidence count and the proved triple-corner exclusion
then determine the two double corners and their remaining owners.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

open ReflectionSeparation

/-- Transport a unique square corner through any actual square-preserving
congruence of two pieces, without referring to chosen intrinsic placements. -/
theorem unique_corner_count_image (d : SquareDissection) {i j a b : Fin 4}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece j)
    (hS : e '' unitSquare = unitSquare) (hab : e (corner a) = corner b)
    (ha : corner a ∈ d.piece i) (hcount : d.cornerTileCount a = 1) :
    d.cornerTileCount b = 1 := by
  have hunique := N5.unique_corner_of_count_one d hcount ha
  obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood i hunique
  have htarget := N5.relative_neighborhood_map e he hS hab hnear
  have hmem : corner b ∈ d.piece j := by
    rw [← he, ← hab]
    exact mem_image_of_mem e ha
  exact N5.corner_count_one_of_unique_owner d hmem
    (N5.unique_piece_of_relative_neighborhood d j hε htarget)

private theorem corner_count_le_two (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (j : Fin 4) : d.cornerTileCount j ≤ 2 := by
  have hle := d.cornerTileCount_le_three hc j
  have hne : d.cornerTileCount j ≠ 3 := fun h => triple_corner_impossible d hc hN h
  omega

private theorem count_two_owner_different (d : SquareDissection) {s i : Fin 4}
    (hs : d.cornerTileCount s = 2) (hi : corner s ∈ d.piece i) :
    ∃ j : Fin 4, j ≠ i ∧ corner s ∈ d.piece j := by
  obtain ⟨a, b, hab, howners⟩ := N5.split_corner_owners d s hs
  rcases (howners i).mp hi with rfl | rfl
  · exact ⟨b, hab.symm, (howners b).mpr (Or.inr rfl)⟩
  · exact ⟨a, hab, (howners a).mpr (Or.inl rfl)⟩

/-- Horizontal full-pair normalization makes the two right corners double. -/
theorem horizontal_corner_counts (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hBL : corner 0 ∈ d.piece 0)
    (hcount : d.cornerTileCount 0 = 1) (hH : horizontal '' d.piece 0 = d.piece 1) :
    d.cornerTileCount 3 = 1 ∧ d.cornerTileCount 1 = 2 ∧ d.cornerTileCount 2 = 2 := by
  have hHL : horizontal (corner 0) = corner 3 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hTL := unique_corner_count_image d horizontal hH horizontal_image_unitSquare
    hHL hBL hcount
  have hsum := d.cornerIncidenceCount_eq_sum_cornerTileCount.symm.trans hN
  rw [CornerCounting.sum_fin_four, hcount, hTL] at hsum
  have h₁ := corner_count_le_two d hc hN 1
  have h₂ := corner_count_le_two d hc hN 2
  exact ⟨hTL, by omega, by omega⟩

/-- Each right corner has an owner among the two pieces outside the
horizontal full pair. -/
theorem horizontal_remaining_owners (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) (hBL : corner 0 ∈ d.piece 0)
    (hBR : corner 1 ∈ d.piece 0) (hcount : d.cornerTileCount 0 = 1)
    (hH : horizontal '' d.piece 0 = d.piece 1) :
    (corner 1 ∈ d.piece 2 ∨ corner 1 ∈ d.piece 3) ∧
      (corner 2 ∈ d.piece 2 ∨ corner 2 ∈ d.piece 3) := by
  obtain ⟨_, hBRcount, hTRcount⟩ := horizontal_corner_counts d hc hN hBL hcount hH
  have hHL : horizontal (corner 0) = corner 3 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hHR : horizontal (corner 1) = corner 2 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hTL : corner 3 ∈ d.piece 1 := by
    rw [← hH, ← hHL]
    exact mem_image_of_mem horizontal hBL
  have hTR : corner 2 ∈ d.piece 1 := by
    rw [← hH, ← hHR]
    exact mem_image_of_mem horizontal hBR
  have hBRnot : corner 1 ∉ d.piece 1 := by
    intro h
    exact d.no_opposite_corners hc 1 1 ⟨h, hTL⟩
  have hTRnot : corner 2 ∉ d.piece 0 := by
    intro h
    exact d.no_opposite_corners hc 0 0 ⟨hBL, h⟩
  constructor
  · obtain ⟨i, hi0, hi⟩ := count_two_owner_different d hBRcount hBR
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hBRnot hi).elim
    · exact Or.inl hi
    · exact Or.inr hi
  · obtain ⟨i, hi1, hi⟩ := count_two_owner_different d hTRcount hTR
    fin_cases i
    · exact (hTRnot hi).elim
    · exact (hi1 rfl).elim
    · exact Or.inl hi
    · exact Or.inr hi

/-- In the adjacent full-pair normalization, the unoccupied corner is
double and the two remaining pieces both own it. -/
theorem antidiagonal_remaining_owners (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hcount : d.cornerTileCount 0 = 1)
    (hA : antiDiagonal '' d.piece 0 = d.piece 1) :
    corner 3 ∈ d.piece 2 ∧ corner 3 ∈ d.piece 3 := by
  classical
  have hAL : antiDiagonal (corner 0) = corner 2 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hAR : antiDiagonal (corner 1) = corner 1 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hTRcount := unique_corner_count_image d antiDiagonal hA
    antiDiagonal_image_unitSquare hAL hBL hcount
  have hBR₁ : corner 1 ∈ d.piece 1 := by
    rw [← hA, ← hAR]
    exact mem_image_of_mem antiDiagonal hBR
  have hsum := d.cornerIncidenceCount_eq_sum_cornerTileCount.symm.trans hN
  rw [CornerCounting.sum_fin_four, hcount, hTRcount] at hsum
  have h₁ := corner_count_le_two d hc hN 1
  have h₃ := corner_count_le_two d hc hN 3
  have hTLcount : d.cornerTileCount 3 = 2 := by omega
  have hnot0 : corner 3 ∉ d.piece 0 := by
    intro h
    exact d.no_opposite_corners hc 0 1 ⟨hBR, h⟩
  have hnot1 : corner 3 ∉ d.piece 1 := by
    intro h
    exact d.no_opposite_corners hc 1 1 ⟨hBR₁, h⟩
  obtain ⟨i, j, hij, howners⟩ := N5.split_corner_owners d 3 hTLcount
  have hi : corner 3 ∈ d.piece i := (howners i).mpr (Or.inl rfl)
  have hj : corner 3 ∈ d.piece j := (howners j).mpr (Or.inr rfl)
  have hi0 : i ≠ 0 := fun h => hnot0 (h ▸ hi)
  have hi1 : i ≠ 1 := fun h => hnot1 (h ▸ hi)
  have hj0 : j ≠ 0 := fun h => hnot0 (h ▸ hj)
  have hj1 : j ≠ 1 := fun h => hnot1 (h ▸ hj)
  have hi23 : i = 2 ∨ i = 3 := by
    fin_cases i <;> simp_all
  have hj23 : j = 2 ∨ j = 3 := by
    fin_cases j <;> simp_all
  rcases hi23 with rfl | rfl <;> rcases hj23 with rfl | rfl
  · exact (hij rfl).elim
  · exact ⟨hi, hj⟩
  · exact ⟨hj, hi⟩
  · exact (hij rfl).elim

end Puzzling139335.N6.TwoDouble
