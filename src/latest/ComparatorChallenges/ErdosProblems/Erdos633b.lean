import Erdos633b.Geometry

namespace Erdos633b

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
