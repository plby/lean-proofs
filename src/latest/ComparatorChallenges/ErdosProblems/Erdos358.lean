/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset

namespace Erdos358

/-- Pairs of positive endpoints whose corresponding consecutive `A`-sum is `n`. -/
def intervalRepresentations (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, A i}

/-- The number of representations of `n` as a sum of consecutive terms of `A`. -/
noncomputable def f (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentations A n)

theorem erdos_358 :
    ∃ A, StrictMono A ∧ atTop.Tendsto (Erdos358.f A) atTop := by
  sorry

theorem erdos_358_part_ii :
    ∃ A, StrictMono A ∧
      ∀ᶠ n in atTop, 2 ≤ Erdos358.f A n := by
  sorry
