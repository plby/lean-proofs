import ErdosProblems.Erdos633b.Geometry

/-!
# The eight independent geometric conditions in the Erdős 633 target

No tiling hypothesis occurs in `EightCases`. Proving its equivalence with
`HasNonsquareTiling` remains the main task; this file is only the specification.
-/

namespace Erdos633b

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

/-- The ordering of the angles is existential; side indices match angle indices. -/
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

theorem eightCases_move_iff (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    EightCases (T.move g) ↔ EightCases T := by
  simp only [EightCases, Triangle.angle_move, Triangle.side_move]

end Erdos633b
