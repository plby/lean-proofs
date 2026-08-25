import StackExchange.Puzzling139335.N6.TwoDouble.NormalizedTypes
import StackExchange.Puzzling139335.N6.TwoDouble.AdjacentCounting
import StackExchange.Puzzling139335.N5.TwoCorner
import StackExchange.Puzzling139335.RectangularHull.FullSide
import StackExchange.Puzzling139335.ReflectionSeparation

/-!
# Actual sides and counts for the horizontal acute-singleton branch

Reflection separation puts the lower outer piece below the midline. The
proved height barrier and half-band saturation force its full bottom side;
the actual reflection then supplies the full top side of the other piece.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N6.TwoDouble.HorizontalAcute

open ReflectionSeparation

noncomputable section

theorem horizontal_corner_zero : horizontal (corner 0) = corner 3 := by
  ext i
  fin_cases i <;> norm_num [corner, Fin.ext_iff]

theorem horizontal_corner_one : horizontal (corner 1) = corner 2 := by
  ext i
  fin_cases i <;> norm_num [corner, Fin.ext_iff]

theorem horizontal_corner_two : horizontal (corner 2) = corner 1 := by
  ext i
  fin_cases i <;> norm_num [corner, Fin.ext_iff]

theorem top_left (d : SquareDissection) (hBL : corner 0 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1) : corner 3 ∈ d.piece 1 := by
  rw [← hQ]
  exact ⟨corner 0, hBL, horizontal_corner_zero⟩

/-- Six incidences and the four named side contacts force both middle
pieces to have exactly one square corner. -/
theorem singleton_counts (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3) :
    d.tileCornerCount 2 = 1 ∧ d.tileCornerCount 3 = 1 := by
  classical
  have hzero := N5.count_two_of_two_corners d hc 0 (by decide) hBL hBR
  have hone := N5.count_two_of_two_corners d hc 1 (by decide)
    (top_left d hBL hQ) (normalized_top_right d hBR hQ)
  have htwo : 0 < d.tileCornerCount 2 := by
    change 0 < (Finset.univ.filter fun j => corner j ∈ d.piece 2).card
    exact Finset.card_pos.mpr ⟨1, by simp [hH]⟩
  have hthree : 0 < d.tileCornerCount 3 := by
    change 0 < (Finset.univ.filter fun j => corner j ∈ d.piece 3).card
    exact Finset.card_pos.mpr ⟨2, by simp [hG]⟩
  have hsum : (∑ i, d.tileCornerCount i) = 6 :=
    d.cornerIncidenceCount_eq_sum_tileCornerCount.symm.trans hN
  rw [CornerCounting.sum_fin_four, hzero, hone] at hsum
  omega

theorem lower_height (d : SquareDissection)
    (hBL : corner 0 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1) :
    ∀ p ∈ d.piece 0, p 1 ≤ (1 / 2 : ℝ) := by
  exact fun _ hp => (d.horizontal_pair_halves_of_bottom_left (by decide) hQ hBL).1 hp

/-- The entire source bottom side belongs to the actual lower piece. -/
theorem full_bottom_side (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1) :
    segment ℝ (corner 0) (corner 1) ⊆ d.piece 0 := by
  simpa [corner, Schoenflies.Plane.mk] using
    RectangularHull.lower_outer_piece_contains_bottom_side d hc
      (le_refl (1 / 2 : ℝ))
      (show Schoenflies.Plane.mk 0 0 ∈ d.piece 0 by
        simpa [corner, Schoenflies.Plane.mk] using hBL)
      (show Schoenflies.Plane.mk 1 0 ∈ d.piece 0 by
        simpa [corner, Schoenflies.Plane.mk] using hBR)
      (lower_height d hBL hQ)

/-- The full source top side is the actual image of the full bottom side. -/
theorem full_top_side (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1) :
    segment ℝ (corner 2) (corner 3) ⊆ d.piece 1 := by
  have hbottom : segment ℝ (corner 1) (corner 0) ⊆ d.piece 0 := by
    simpa only [segment_symm] using full_bottom_side d hc hBL hBR hQ
  have himage := image_mono (f := horizontal) hbottom
  have hsegment : horizontal '' segment ℝ (corner 1) (corner 0) =
      segment ℝ (corner 2) (corner 3) := by
    have hs : horizontal '' segment ℝ (corner 1) (corner 0) =
        segment ℝ (horizontal (corner 1)) (horizontal (corner 0)) :=
      image_segment ℝ horizontal.toAffineMap (corner 1) (corner 0)
    simpa only [horizontal_corner_one, horizontal_corner_zero] using hs
  simpa only [hsegment, hQ] using himage

/-- A source placement at the upper right corner becomes an actual
corner-fixing congruence from the reflected outer piece. -/
theorem top_fixing_placement (d : SquareDissection)
    (hQ : horizontal '' d.piece 0 = d.piece 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (heBR : e (corner 1) = corner 2) :
    (horizontal.trans e) '' d.piece 1 = d.piece 3 ∧
      (horizontal.trans e) (corner 2) = corner 2 := by
  constructor
  · rw [← hQ, image_image]
    calc
      (fun p => (horizontal.trans e) (horizontal p)) '' d.piece 0 = e '' d.piece 0 := by
        congr 1
        funext p
        change e (horizontal (horizontal p)) = e p
        rw [horizontal_involutive]
      _ = d.piece 3 := he
  · change e (horizontal (corner 2)) = corner 2
    rw [horizontal_corner_two, heBR]

/-- The named pair exhausts the bottom-right corner. -/
theorem bottom_other_not_mem (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) (hBR : corner 1 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3) :
    ∀ l, l ≠ 0 → l ≠ 2 → corner 1 ∉ d.piece l := by
  have hcounts := normalized_corner_counts_of_distinct_owners d hN
    (by decide : (0 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3)
    hBR (normalized_top_right d hBR hQ) hH hG
  intro l hl0 hl2
  exact other_not_mem_of_two_owners d (by decide) hBR hH hcounts.2.1 hl0 hl2

/-- The named pair exhausts the top-right corner. -/
theorem top_other_not_mem (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) (hBR : corner 1 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3) :
    ∀ l, l ≠ 1 → l ≠ 3 → corner 2 ∉ d.piece l := by
  have hcounts := normalized_corner_counts_of_distinct_owners d hN
    (by decide : (0 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3)
    hBR (normalized_top_right d hBR hQ) hH hG
  intro l hl1 hl3
  exact other_not_mem_of_two_owners d (by decide)
    (normalized_top_right d hBR hQ) hG hcounts.2.2.1 hl1 hl3

end

end Puzzling139335.N6.TwoDouble.HorizontalAcute
