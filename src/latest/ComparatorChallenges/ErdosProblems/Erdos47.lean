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
open Filter Finset Real
open scoped ArithmeticFunction.omega BigOperators

namespace Erdos47

open scoped Classical in
theorem erdos47_bloom :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      C * ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)) < rec_sum A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  sorry


open scoped Classical in
theorem erdos47 :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      δ * log N < rec_sum A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  sorry

end Erdos47
