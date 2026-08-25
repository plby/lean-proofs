import StackExchange.Puzzling139335.InitialReduction
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Exact corner data for the normalized adjacent pair

The first piece owns the bottom side endpoints, and its anti-diagonal
reflection is the second piece.  The other two pieces contain the top-left
corner.  Six total incidences force all remaining corner memberships.
Every count here concerns the actual closed pieces.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N6.TwoDouble.Adjacent

/-- The complete corner-incidence table in the adjacent normalization. -/
structure NormalizedCornerData (d : SquareDissection) : Prop where
  corner_zero_iff : ∀ i, corner 0 ∈ d.piece i ↔ i = 0
  corner_one_iff : ∀ i, corner 1 ∈ d.piece i ↔ i = 0 ∨ i = 1
  corner_two_iff : ∀ i, corner 2 ∈ d.piece i ↔ i = 1
  corner_three_iff : ∀ i, corner 3 ∈ d.piece i ↔ i = 2 ∨ i = 3
  corner_count_zero : d.cornerTileCount 0 = 1
  corner_count_one : d.cornerTileCount 1 = 2
  corner_count_two : d.cornerTileCount 2 = 1
  corner_count_three : d.cornerTileCount 3 = 2
  tile_count_zero : d.tileCornerCount 0 = 2
  tile_count_one : d.tileCornerCount 1 = 2
  tile_count_two : d.tileCornerCount 2 = 1
  tile_count_three : d.tileCornerCount 3 = 1

private theorem owner_iff_of_count_one (d : SquareDissection) {i j : Fin 4}
    (hc : d.cornerTileCount j = 1) (hi : corner j ∈ d.piece i) (k : Fin 4) :
    corner j ∈ d.piece k ↔ k = i := by
  classical
  constructor
  · intro hk
    change (Finset.univ.filter fun l => corner j ∈ d.piece l).card = 1 at hc
    exact Finset.card_le_one_iff.mp hc.le (by simp [hk]) (by simp [hi])
  · rintro rfl
    exact hi

/-- The normalized geometric memberships determine the entire corner table.
In particular, the two pieces meeting at top left each contain just one
physical square corner. -/
theorem normalized_corner_data (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hanti : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 1)
    (hTL2 : corner 3 ∈ d.piece 2) (hTL3 : corner 3 ∈ d.piece 3) :
    NormalizedCornerData d := by
  classical
  have hantiBR : ReflectionSeparation.antiDiagonal (corner 1) = corner 1 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hantiBL : ReflectionSeparation.antiDiagonal (corner 0) = corner 2 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hBR1 : corner 1 ∈ d.piece 1 := by
    rw [← hanti]
    exact ⟨corner 1, hBR, hantiBR⟩
  have hTR1 : corner 2 ∈ d.piece 1 := by
    rw [← hanti]
    exact ⟨corner 0, hBL, hantiBL⟩
  have hnTL0 : corner 3 ∉ d.piece 0 := by
    simpa using d.opposite_corner_not_mem hc 0 1 hBR
  have hnTL1 : corner 3 ∉ d.piece 1 := by
    simpa using d.opposite_corner_not_mem hc 1 1 hBR1
  have hnBR2 : corner 1 ∉ d.piece 2 := by
    simpa using d.opposite_corner_not_mem hc 2 3 hTL2
  have hnBR3 : corner 1 ∉ d.piece 3 := by
    simpa using d.opposite_corner_not_mem hc 3 3 hTL3
  have hBRiff (i : Fin 4) : corner 1 ∈ d.piece i ↔ i = 0 ∨ i = 1 := by
    fin_cases i
    · simp [hBR]
    · simp [hBR1]
    · simp [hnBR2]
    · simp [hnBR3]
  have hTLiff (i : Fin 4) : corner 3 ∈ d.piece i ↔ i = 2 ∨ i = 3 := by
    fin_cases i
    · simp [hnTL0]
    · simp [hnTL1]
    · simp [hTL2]
    · simp [hTL3]
  have hBRcount : d.cornerTileCount 1 = 2 := by
    change (Finset.univ.filter fun i => corner 1 ∈ d.piece i).card = 2
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, CornerCounting.sum_fin_four]
    simp [hBRiff]
  have hTLcount : d.cornerTileCount 3 = 2 := by
    change (Finset.univ.filter fun i => corner 3 ∈ d.piece i).card = 2
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, CornerCounting.sum_fin_four]
    simp [hTLiff]
  have hsum := d.cornerIncidenceCount_eq_sum_cornerTileCount
  rw [CornerCounting.sum_fin_four] at hsum
  have hBLpos := d.cornerTileCount_pos 0
  have hTRpos := d.cornerTileCount_pos 2
  have hBLcount : d.cornerTileCount 0 = 1 := by omega
  have hTRcount : d.cornerTileCount 2 = 1 := by omega
  have hBLiff := owner_iff_of_count_one d hBLcount hBL
  have hTRiff := owner_iff_of_count_one d hTRcount hTR1
  refine
    { corner_zero_iff := hBLiff
      corner_one_iff := hBRiff
      corner_two_iff := hTRiff
      corner_three_iff := hTLiff
      corner_count_zero := hBLcount
      corner_count_one := hBRcount
      corner_count_two := hTRcount
      corner_count_three := hTLcount
      tile_count_zero := ?_
      tile_count_one := ?_
      tile_count_two := ?_
      tile_count_three := ?_ }
  all_goals
    change (Finset.univ.filter fun j => corner j ∈ d.piece _).card = _
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, CornerCounting.sum_fin_four]
    simp [hBLiff, hBRiff, hTRiff, hTLiff]

namespace NormalizedCornerData

variable {d : SquareDissection} (h : NormalizedCornerData d)

include h

/-- Only the first two pieces contain bottom right. -/
theorem only_bottom_right (l : Fin 4) (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    corner 1 ∉ d.piece l := by
  intro hl
  rcases (h.corner_one_iff l).mp hl with heq | heq
  · exact hl0 heq
  · exact hl1 heq

/-- Only the last two pieces contain top left. -/
theorem only_top_left (l : Fin 4) (hl2 : l ≠ 2) (hl3 : l ≠ 3) :
    corner 3 ∉ d.piece l := by
  intro hl
  rcases (h.corner_three_iff l).mp hl with heq | heq
  · exact hl2 heq
  · exact hl3 heq

/-- The first piece uniquely owns bottom left. -/
theorem only_bottom_left (l : Fin 4) (hl0 : l ≠ 0) :
    corner 0 ∉ d.piece l :=
  fun hl => hl0 ((h.corner_zero_iff l).mp hl)

/-- The second piece uniquely owns top right. -/
theorem only_top_right (l : Fin 4) (hl1 : l ≠ 1) :
    corner 2 ∉ d.piece l :=
  fun hl => hl1 ((h.corner_two_iff l).mp hl)

/-- Either remaining piece contains exactly the top-left physical corner. -/
theorem singleton_corner_iff (k : Fin 4) (hk : k = 2 ∨ k = 3) (j : Fin 4) :
    corner j ∈ d.piece k ↔ j = 3 := by
  rcases hk with rfl | rfl <;> fin_cases j <;>
    simp [h.corner_zero_iff, h.corner_one_iff, h.corner_two_iff, h.corner_three_iff]

/-- Both remaining pieces have corner count one. -/
theorem singleton_tile_count (k : Fin 4) (hk : k = 2 ∨ k = 3) :
    d.tileCornerCount k = 1 := by
  rcases hk with rfl | rfl
  · exact h.tile_count_two
  · exact h.tile_count_three

end NormalizedCornerData

end Puzzling139335.N6.TwoDouble.Adjacent
