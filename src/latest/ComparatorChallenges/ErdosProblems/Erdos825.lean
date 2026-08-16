/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 825

Benkoski and Erdős asked whether sufficiently large abundancy forces an
integer to be a sum of distinct proper divisors.
-/

open scoped ArithmeticFunction.sigma BigOperators List

syntax (name := answerSyntax825) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace Erdos825

noncomputable section

/-- The exact proper-divisor conclusion occurring in the formal conjecture. -/
def Pseudoperfect (n : ℕ) : Prop :=
  ∃ s ⊆ n.properDivisors, n = s.sum id

theorem erdos_825 :
    answer(True) ↔ ∃ (C : ℝ) (_ : C > 0),
      ∀ (n) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id := by
  sorry
