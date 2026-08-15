/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos615.Erdos615Construction

open Filter SimpleGraph Set Real
open scoped Topology BigOperators ENNReal NNReal

namespace Erdos615

syntax (name := answerSyntax615) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

attribute [local instance] Classical.propDecidable

open Construction

theorem erdos_615 : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in atTop,
      ∀ G : SimpleGraph (Fin n), (1 / 8 - c) * n ^ 2 ≤ G.edgeFinset.card →
        ¬ G.CliqueFree 4 ∨ (n : ℝ) / Real.log n ≤ G.indepNum := by
  sorry

