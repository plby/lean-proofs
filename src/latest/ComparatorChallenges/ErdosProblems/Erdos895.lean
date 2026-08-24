/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 895

This file formalizes the sharp finite resolution reported by Ben Barber:
every triangle-free graph on the labelled vertices `{1, ..., n}`, with
`n ≥ 18`, contains three distinct independent vertices `a`, `b`, `a + b`.

Lean vertex `i : Fin n` represents the mathematical label `i.val + 1`.
-/

namespace Erdos895

/-- The exact distinct-summand configuration in zero-based `Fin n` coordinates.

If Lean's vertices `a` and `b` have mathematical labels `a.val + 1` and
`b.val + 1`, their sum has `Fin` value `a.val + b.val + 1`. -/
def HasIndependentSchurTriple {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (a b : Fin n) (hsum : a.val + b.val + 1 < n),
    a.val < b.val ∧
      ¬G.Adj a b ∧
      ¬G.Adj a ⟨a.val + b.val + 1, hsum⟩ ∧
      ¬G.Adj b ⟨a.val + b.val + 1, hsum⟩

theorem erdos_895 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 → HasIndependentSchurTriple G := by
  sorry

end Erdos895
