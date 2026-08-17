/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization of the negative answer to Erdős Problem 533.

The mathematical construction is the `p = 3`, `ℓ = 1` specialization of
the complex Bollobás--Erdős graph of Liu, Reiher, Sharifzadeh, and Staden.
-/

import Mathlib

open Filter SimpleGraph
open Set MeasureTheory
open scoped Classical ENNReal NNReal Pointwise Topology BigOperators

syntax (name := answerSyntax533) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace Erdos533

/-! ## The complex sphere used by the LRSS construction -/

theorem erdos_533 : answer(False) ↔
    ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          ∃ S : Finset (Fin n), c * n ≤ (S.card : ℝ) ∧
            G.CliqueFreeOn (S : Set (Fin n)) 3 := by
  sorry
