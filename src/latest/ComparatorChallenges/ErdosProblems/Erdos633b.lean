import Mathlib

namespace Erdos633b

abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev Triangle := Affine.Triangle ℝ Plane

namespace Triangle

def support (T : Triangle) : Set Plane := convexHull ℝ (Set.range T.points)

noncomputable def angle (T : Triangle) (i : Fin 3) : ℝ :=
  EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2))

noncomputable def side (T : Triangle) (i : Fin 3) : ℝ :=
  dist (T.points (i + 1)) (T.points (i + 2))

end Triangle

structure Tiling (T : Triangle) (n : ℕ) where
  tile : Triangle
  place : Fin n → Plane ≃ᵃⁱ[ℝ] Plane
  covers : (⋃ i, place i '' tile.support) = T.support
  disjoint_interiors : Pairwise fun i j =>
    Disjoint (interior (place i '' tile.support)) (interior (place j '' tile.support))

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

def EightCases (T : Triangle) : Prop :=
  ∃ e : Equiv.Perm (Fin 3),
    let A := T.angle (e 0)
    let B := T.angle (e 1)
    let C := T.angle (e 2)
    (A = B) ∨
    (C = Real.pi / 2 ∧ ∃ M K : ℕ, 0 < M ∧ 0 < K ∧
      T.side (e 0) / T.side (e 1) = (M : ℝ) / K ∧ ¬ IsSquare (M ^ 2 + K ^ 2)) ∨
    (A = Real.pi / 6 ∧ B = Real.pi / 2 ∧ C = Real.pi / 3) ∨
    (C = Real.pi / 3 ∧ IsRational (Real.sqrt 3 * Real.tan (A / 2))) ∨
    (B = 2 * A ∧ IsRational (Real.sqrt 3 * Real.tan (A / 2))) ∨
    (B = 2 * A ∧ IsRational (Real.sin (A / 2))) ∨
    (C = A / 2 + B ∧ ∃ M K : ℕ, 0 < M ∧ 0 < K ∧
      2 * Real.sin (A / 4) = (M : ℝ) / K ∧
      ¬ IsSquare (2 * (K : ℤ) ^ 2 - (M : ℤ) ^ 2)) ∨
    (C = 2 * A + B / 2 ∧ IsRational (Real.sqrt 3 * Real.tan (A / 2)))

theorem erdos_633 (T : Triangle) :
    (∃ n : ℕ, ¬ IsSquare n ∧ Nonempty (Tiling T n)) ↔ EightCases T := by
  sorry

theorem erdos_633_only_square (T : Triangle) :
    (∀ n : ℕ, Nonempty (Tiling T n) → IsSquare n) ↔ ¬ EightCases T := by
  sorry

end Erdos633b
