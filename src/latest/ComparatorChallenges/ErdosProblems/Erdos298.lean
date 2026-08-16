import Mathlib

namespace UnitFractions

open scoped BigOperators
open Filter Real Finset Nat
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

section

variable (A : Set ℕ)

def partial_density (N : ℕ) : ℝ := ((range N).filter fun n ↦ n ∈ A).card / N
def upper_density : ℝ := limsup (partial_density A) atTop
def lower_density : ℝ := liminf (partial_density A) atTop
def has_density (d : ℝ) : Prop := upper_density A = d ∧ lower_density A = d
variable {A}

end

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n
namespace Nat

end Nat

end

end UnitFractions

attribute [local instance] Classical.propDecidable

open UnitFractions

namespace Erdos298

theorem erdos298 (A : Set ℕ) (hA : 0 < upper_density A) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ rec_sum S = 1 := by
  sorry


theorem erdos298_density (A : Set ℕ) (d : ℝ) (hA : has_density A d) (hd : 0 < d) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ rec_sum S = 1 := by
  sorry

end Erdos298
