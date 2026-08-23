/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace UnitFractions

open scoped BigOperators
open Filter Real Finset Nat
open _root_.Finset

noncomputable section

section

variable (A : Set ℕ)

variable {A}

end

open scoped Classical in
def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n
namespace Nat

end Nat

end

end UnitFractions

open UnitFractions

namespace Erdos45

open scoped Classical in
theorem erdos45 :
    ∀ k : ℕ, 2 ≤ k → ∃ nₖ : ℕ, ∀ c : ℕ → Fin k,
      ∃ D' : Finset ℕ, D' ⊆ ((nₖ.divisors.erase 1).erase nₖ) ∧
        rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a := by
  sorry

end Erdos45
