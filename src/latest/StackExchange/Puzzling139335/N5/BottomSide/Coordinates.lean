import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.RectangularHull.Interlacing.SquareBoundary

/-!
# Coordinates of the bottom and left square sides
-/

open Set

namespace Puzzling139335.N5

theorem bottom_segment_coordinates {z : Plane} :
    z ∈ segment ℝ (corner 0) (corner 1) ↔ z 1 = 0 ∧ 0 ≤ z 0 ∧ z 0 ≤ 1 := by
  change z ∈ segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ↔ _
  simp only [Schoenflies.mem_segment_horiz,
    segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num), mem_Icc]

theorem left_segment_coordinates {z : Plane} :
    z ∈ segment ℝ (corner 0) (corner 3) ↔ z 0 = 0 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
  change z ∈ segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 1) ↔ _
  simp only [Schoenflies.mem_segment_vert,
    segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num), mem_Icc]

theorem bottom_open_coordinates {z : Plane}
    (hz : z ∈ segment ℝ (corner 0) (corner 1) \ {corner 0, corner 1}) :
    z 1 = 0 ∧ 0 < z 0 ∧ z 0 < 1 := by
  obtain ⟨hz1, hz0, hz0'⟩ := bottom_segment_coordinates.mp hz.1
  have hne0 : z 0 ≠ 0 := by
    intro h
    apply hz.2
    apply mem_insert_iff.mpr
    left
    ext k
    fin_cases k
    · exact h
    · exact hz1
  have hne1 : z 0 ≠ 1 := by
    intro h
    apply hz.2
    apply mem_insert_iff.mpr
    right
    apply mem_singleton_iff.mpr
    ext k
    fin_cases k
    · exact h
    · exact hz1
  exact ⟨hz1, lt_of_le_of_ne hz0 hne0.symm, lt_of_le_of_ne hz0' hne1⟩

theorem diagonal_mem_left_segment_iff {z : Plane} :
    ReflectionSeparation.diagonal z ∈ segment ℝ (corner 0) (corner 3) ↔
      z ∈ segment ℝ (corner 0) (corner 1) := by
  simp only [left_segment_coordinates, bottom_segment_coordinates,
    ReflectionSeparation.diagonal_apply_zero, ReflectionSeparation.diagonal_apply_one]

theorem diagonal_mem_bottom_segment_iff {z : Plane} :
    ReflectionSeparation.diagonal z ∈ segment ℝ (corner 0) (corner 1) ↔
      z ∈ segment ℝ (corner 0) (corner 3) := by
  simp only [bottom_segment_coordinates, left_segment_coordinates,
    ReflectionSeparation.diagonal_apply_zero, ReflectionSeparation.diagonal_apply_one]

theorem diagonal_bottom_open_left {z : Plane}
    (hz : z ∈ segment ℝ (corner 0) (corner 1) \ {corner 0, corner 1}) :
    ReflectionSeparation.diagonal z ∈
      segment ℝ (corner 0) (corner 3) \ {corner 0, corner 3} := by
  refine ⟨diagonal_mem_left_segment_iff.mpr hz.1, ?_⟩
  have hfix : ReflectionSeparation.diagonal (corner 0) = corner 0 :=
    ReflectionSeparation.diagonal_fixed rfl
  have hswap : ReflectionSeparation.diagonal (corner 1) = corner 3 := by
    ext k
    fin_cases k <;> norm_num [corner, Fin.ext_iff]
  intro hends
  apply hz.2
  rcases mem_insert_iff.mp hends with hzero | hthree
  · exact mem_insert_iff.mpr (Or.inl
      (ReflectionSeparation.diagonal.injective (hzero.trans hfix.symm)))
  · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr
      (ReflectionSeparation.diagonal.injective
        ((mem_singleton_iff.mp hthree).trans hswap.symm))))

end Puzzling139335.N5
