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
open Filter Finset Real
open scoped ArithmeticFunction.omega BigOperators

namespace Erdos47

theorem erdos47_bloom :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      C * ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)) < rec_sum A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  sorry


theorem erdos47 :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      δ * log N < rec_sum A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  sorry

end Erdos47
