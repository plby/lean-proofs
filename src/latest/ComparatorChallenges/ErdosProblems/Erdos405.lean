/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the resolution of Erdős Problem 405.
https://www.erdosproblems.com/405

Informal authors:
- Béla Brindza
- Paul Erdős
- Kunrui Yu
- Dehua Liu
- Maohua Le

Formal authors:
- Codex

The main theorem `erdos405_iff` classifies all positive-integer solutions of

  (p - 1)! + a^(p - 1) = p^k

with `p` an odd prime.
-/

import Mathlib

namespace Erdos405

/-- A positive-integer solution of the equation in Erdős Problem 405. -/
def IsSolution (p a k : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ 0 < a ∧ 0 < k ∧
    (p - 1).factorial + a ^ (p - 1) = p ^ k

/-- The three triples found by Yu--Liu and Le. -/
def exceptionalSolutions : Finset (ℕ × ℕ × ℕ) :=
  {(3, 1, 1), (3, 5, 3), (5, 1, 2)}

@[simp] theorem isSolution_three_one_one : IsSolution 3 1 1 := by
  norm_num [IsSolution, Nat.factorial]

@[simp] theorem isSolution_three_five_three : IsSolution 3 5 3 := by
  norm_num [IsSolution, Nat.factorial]

@[simp] theorem isSolution_five_one_two : IsSolution 5 1 2 := by
  norm_num [IsSolution, Nat.factorial]

theorem erdos405_iff {p a k : ℕ} :
    IsSolution p a k ↔
      (p = 3 ∧ a = 1 ∧ k = 1) ∨
      (p = 3 ∧ a = 5 ∧ k = 3) ∨
      (p = 5 ∧ a = 1 ∧ k = 2) := by
  sorry

end Erdos405
