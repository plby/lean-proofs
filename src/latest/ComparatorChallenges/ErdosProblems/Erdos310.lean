/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 310: bounded-denominator reciprocal subsums of dense finite sets.

The mathematical proof and Leanization plan are in `tex/310.tex` at the
repository root.  The analytic input below is Bloom's theorem, already proved
in the repository's `UnitFractions` development.
-/

import Mathlib

open Filter Real
open scoped ArithmeticFunction.omega BigOperators

namespace Erdos310

open Finset

/-- The explicit reciprocal sum used in the problem is `UnitFractions.rec_sum`. -/


theorem erdos_310 :
    ∀ α : ℝ, 0 < α →
      ∃ C : ℕ, 1 ≤ C ∧
        ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ Icc 1 N →
          α * N ≤ A.card →
            ∃ S : Finset ℕ, S ⊆ A ∧ S.Nonempty ∧
              ∃ a b : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ C ∧
                S.sum (fun n => (1 / n : ℚ)) = a / b := by
  sorry

end Erdos310
