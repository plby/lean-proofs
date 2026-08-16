import Mathlib

namespace UnitFractions

open scoped BigOperators
open Filter Real Finset Nat
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

section

variable (A : Set ℕ)

variable {A}

end

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n
namespace Nat

end Nat

end

end UnitFractions

attribute [local instance] Classical.propDecidable

open UnitFractions

namespace Erdos45

theorem erdos45 :
    ∀ k : ℕ, 2 ≤ k → ∃ nₖ : ℕ, ∀ c : ℕ → Fin k,
      ∃ D' : Finset ℕ, D' ⊆ ((nₖ.divisors.erase 1).erase nₖ) ∧
        rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a := by
  sorry

end Erdos45
