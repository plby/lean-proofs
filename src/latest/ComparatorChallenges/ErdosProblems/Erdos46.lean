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

namespace Erdos46

theorem erdos46 :
    ∀ {α : Type*} [Finite α] (c : ℤ → α),
      ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧ rec_sum S = 1 ∧ ∃ a : α, ∀ n ∈ S, c (n : ℤ) = a := by
  sorry

end Erdos46
