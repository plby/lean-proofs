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

namespace Erdos46

open scoped Classical in
theorem erdos46 :
    ∀ {α : Type*} [Finite α] (c : ℤ → α),
      ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧ rec_sum S = 1 ∧ ∃ a : α, ∀ n ∈ S, c (n : ℤ) = a := by
  sorry

end Erdos46
