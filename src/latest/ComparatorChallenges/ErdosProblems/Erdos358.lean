/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 358

This file formalizes the statement from
`google-deepmind/formal-conjectures/FormalConjectures/ErdosProblems/358.lean`.
The mathematical construction is described in detail in `tex/358.tex`.
-/

open scoped BigOperators Topology

namespace Erdos358

open Filter Finset

syntax (name := answerSyntax358) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

/-- Pairs of positive endpoints whose corresponding consecutive `A`-sum is `n`. -/
def intervalRepresentations (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, A i}

/-- The number of representations of `n` as a sum of consecutive terms of `A`. -/
noncomputable def f (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentations A n)

theorem erdos_358.parts.i :
    answer(True) ↔ ∃ A, StrictMono A ∧ atTop.Tendsto (Erdos358.f A) atTop := by
  sorry

theorem erdos_358.parts.ii :
    answer(True) ↔ ∃ A, StrictMono A ∧
      ∀ᶠ n in atTop, 2 ≤ Erdos358.f A n := by
  sorry
