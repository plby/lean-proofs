/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos405

/-- A positive-integer solution of the equation in Erdős Problem 405. -/
def IsSolution (p a k : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ 0 < a ∧ 0 < k ∧
    (p - 1).factorial + a ^ (p - 1) = p ^ k

theorem erdos_405 {p a k : ℕ} :
    IsSolution p a k ↔
      (p = 3 ∧ a = 1 ∧ k = 1) ∨
      (p = 3 ∧ a = 5 ∧ k = 3) ∨
      (p = 5 ∧ a = 1 ∧ k = 2) := by
  sorry

end Erdos405
