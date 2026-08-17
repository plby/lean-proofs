/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter SimpleGraph

namespace Erdos22

syntax (name := answerSyntax22) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

attribute [local instance] Classical.propDecidable

theorem erdos_22 : answer(True) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  sorry
