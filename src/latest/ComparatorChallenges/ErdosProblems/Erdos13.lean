/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

/-!
# Erdős Problem 13
-/

namespace Erdos13

/-- A finite set has property P if none of its elements divides a sum of two
strictly larger elements of the set. -/
def IsForbiddenTripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < min b c → ¬a ∣ b + c

theorem erdos_13 : ∃ C : ℝ, ∀ N : ℕ, ∀ A ⊆ Icc 1 N, IsForbiddenTripleFree A →
    (A.card : ℝ) ≤ (N : ℝ) / 3 + C := by
  sorry
