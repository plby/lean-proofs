/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0.
Definitions adapted from the upstream formalization; modified for this repository. -/
import Mathlib

namespace Erdos865

/-- `A` contains a *pairwise-sum triple*: distinct `a, b, c ∈ A` with
`a+b, a+c, b+c ∈ A`. -/
def HasTriple (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

theorem erdos_865 : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Finset.Icc 1 N → (5 : ℝ) / 8 * N + C ≤ A.card → HasTriple A := by
  sorry

end Erdos865
