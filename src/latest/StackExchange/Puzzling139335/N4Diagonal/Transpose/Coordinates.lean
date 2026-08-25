import StackExchange.Puzzling139335.N4Diagonal.Defs

/-!
# Coordinates under reflection across the main diagonal

Transposition preserves the lower triangle and exchanges its two nonzero
square corners. The complementary angular frame has its first projection
preserved and its perpendicular projection reversed.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ReflectionSeparation ThreeCorners

@[simp] theorem diagonal_zero : diagonal (0 : Plane) = 0 := by
  ext i
  fin_cases i <;> simp

@[simp] theorem diagonal_corner (j : Fin 4) :
    diagonal (corner j) = corner (-j) := by
  fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [corner, Fin.ext_iff, Fin.val_neg']

@[simp] theorem diagonal_mem_lowerTriangle {x : Plane} :
    diagonal x ∈ lowerTriangle ↔ x ∈ lowerTriangle := by
  change (0 ≤ x 1 ∧ 0 ≤ x 0 ∧ x 1 + x 0 ≤ 1) ↔
    (0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1)
  constructor <;> rintro ⟨h₀, h₁, h₂⟩ <;>
    exact ⟨h₁, h₀, by simpa only [add_comm] using h₂⟩

theorem diagonal_antiDiagonal_commute (x : Plane) :
    diagonal (antiDiagonal x) = antiDiagonal (diagonal x) := by
  ext i
  fin_cases i <;> simp

theorem diagonal_ray_sub (t : ℝ) :
    diagonal (ray (Real.pi / 2 - t)) = ray t := by
  ext i
  fin_cases i <;> simp [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

theorem diagonal_perpRay_sub (t : ℝ) :
    diagonal (perpRay (Real.pi / 2 - t)) = -perpRay t := by
  ext i
  fin_cases i <;> simp [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

theorem inner_ray_diagonal_sub (t : ℝ) (x v : Plane) :
    inner ℝ (ray (Real.pi / 2 - t)) (diagonal x - diagonal v) =
      inner ℝ (ray t) (x - v) := by
  simp [Schoenflies.Plane.inner_eq, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub, add_comm]

theorem inner_perpRay_diagonal_sub (t : ℝ) (x v : Plane) :
    inner ℝ (perpRay (Real.pi / 2 - t)) (diagonal x - diagonal v) =
      -inner ℝ (perpRay t) (x - v) := by
  simp [Schoenflies.Plane.inner_eq, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]

end Puzzling139335.N4Diagonal
