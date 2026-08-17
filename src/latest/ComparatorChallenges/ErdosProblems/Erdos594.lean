/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 594

Every graph with no countable proper coloring contains all sufficiently large
odd cycles.
-/

syntax (name := answerSyntax594) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

open Function Set SimpleGraph
open scoped Ordinal

namespace Erdos594

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type*}

end

end Erdos594

theorem erdos_594 : answer(True) ↔
    ∀ (V : Type) (G : SimpleGraph V), IsEmpty (G.Coloring ℕ) →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * k + 1 := by
  sorry
