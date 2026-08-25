import StackExchange.Puzzling139335.CornerIncidence
import StackExchange.Puzzling139335.RectangularHull.Interlacing.SquareBoundary

/-!
# The actual side segments of the unit square

Each segment between consecutive corners is a boundary arc. Among the
four square corners, precisely its two endpoints lie on that segment.
-/

open Set

namespace Puzzling139335.N8

/-- Consecutive square corners are distinct, including the side from `3` to `0`. -/
theorem adjacent_corners_ne (a : Fin 4) : corner a ≠ corner (a + 1) := by
  intro h
  have ha := corner_injective h
  fin_cases a <;> norm_num [Fin.ext_iff, Fin.val_add] at ha

/-- A square side is an actual arc between its two consecutive corners. -/
theorem side_segment_isArcBetween (a : Fin 4) :
    Schoenflies.IsArcBetween (segment ℝ (corner a) (corner (a + 1)))
      (corner a) (corner (a + 1)) :=
  Schoenflies.isArcBetween_segment (adjacent_corners_ne a)

/-- The entire closed segment forming any square side lies on the square frontier. -/
theorem side_segment_subset_frontier_unitSquare (a : Fin 4) :
    segment ℝ (corner a) (corner (a + 1)) ⊆ frontier unitSquare := by
  fin_cases a
  · change segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ _
    exact RectangularHull.bottom_segment_subset_frontier (by norm_num)
      (by norm_num) (by norm_num)
  · intro p hp
    change p ∈ segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 1) at hp
    rw [Schoenflies.mem_segment_vert,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)] at hp
    rw [unitSquare_eq_closedSquare]
    apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
    · change |p 0 - (1 / 2 : ℝ)| = 1 / 2
      rw [hp.1]
      norm_num
    · change |p 1 - (1 / 2 : ℝ)| ≤ 1 / 2
      rw [abs_le]
      constructor <;> linarith [hp.2.1, hp.2.2]
  · intro p hp
    change p ∈ segment ℝ (Schoenflies.Plane.mk 1 1) (Schoenflies.Plane.mk 0 1) at hp
    rw [segment_symm, Schoenflies.mem_segment_horiz,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)] at hp
    rw [unitSquare_eq_closedSquare]
    apply Schoenflies.Plane.mem_frontier_closedSquare_of_snd
    · change |p 1 - (1 / 2 : ℝ)| = 1 / 2
      rw [hp.1]
      norm_num
    · change |p 0 - (1 / 2 : ℝ)| ≤ 1 / 2
      rw [abs_le]
      constructor <;> linarith [hp.2.1, hp.2.2]
  · intro p hp
    change p ∈ segment ℝ (Schoenflies.Plane.mk 0 1) (Schoenflies.Plane.mk 0 0) at hp
    rw [segment_symm, Schoenflies.mem_segment_vert,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)] at hp
    rw [unitSquare_eq_closedSquare]
    apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
    · change |p 0 - (1 / 2 : ℝ)| = 1 / 2
      rw [hp.1]
      norm_num
    · change |p 1 - (1 / 2 : ℝ)| ≤ 1 / 2
      rw [abs_le]
      constructor <;> linarith [hp.2.1, hp.2.2]

/-- Exactly the endpoint corners lie on a given side segment. -/
theorem corner_mem_side_segment_iff (a c : Fin 4) :
    corner c ∈ segment ℝ (corner a) (corner (a + 1)) ↔ c = a ∨ c = a + 1 := by
  fin_cases a
  · change corner c ∈ segment ℝ (Schoenflies.Plane.mk 0 0)
      (Schoenflies.Plane.mk 1 0) ↔ c = 0 ∨ c = 1
    rw [Schoenflies.mem_segment_horiz,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    fin_cases c <;> norm_num [corner, Fin.ext_iff]
  · change corner c ∈ segment ℝ (Schoenflies.Plane.mk 1 0)
      (Schoenflies.Plane.mk 1 1) ↔ c = 1 ∨ c = 2
    rw [Schoenflies.mem_segment_vert,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    fin_cases c <;> norm_num [corner, Fin.ext_iff]
  · change corner c ∈ segment ℝ (Schoenflies.Plane.mk 1 1)
      (Schoenflies.Plane.mk 0 1) ↔ c = 2 ∨ c = 3
    rw [segment_symm, Schoenflies.mem_segment_horiz,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    fin_cases c <;> norm_num [corner, Fin.ext_iff]
  · change corner c ∈ segment ℝ (Schoenflies.Plane.mk 0 1)
      (Schoenflies.Plane.mk 0 0) ↔ c = 3 ∨ c = 0
    rw [segment_symm, Schoenflies.mem_segment_vert,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    fin_cases c <;> norm_num [corner, Fin.ext_iff]

end Puzzling139335.N8
