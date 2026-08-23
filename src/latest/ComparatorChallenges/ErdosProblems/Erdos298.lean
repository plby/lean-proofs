/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace UnitFractions

open scoped BigOperators
open Filter Real Finset Nat
open _root_.Finset

noncomputable section

section

variable (A : Set ℕ)

open scoped Classical in
def partial_density (N : ℕ) : ℝ := ((range N).filter fun n ↦ n ∈ A).card / N
open scoped Classical in
def upper_density : ℝ := limsup (partial_density A) atTop
open scoped Classical in
def lower_density : ℝ := liminf (partial_density A) atTop
open scoped Classical in
def has_density (d : ℝ) : Prop := upper_density A = d ∧ lower_density A = d
variable {A}

end

open scoped Classical in
def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n
namespace Nat

end Nat

end

end UnitFractions


open UnitFractions

namespace Erdos298

open scoped Classical in
theorem erdos298 (A : Set ℕ) (hA : 0 < upper_density A) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ rec_sum S = 1 := by
  sorry


open scoped Classical in
theorem erdos298_density (A : Set ℕ) (d : ℝ) (hA : has_density A d) (hd : 0 < d) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ rec_sum S = 1 := by
  sorry

end Erdos298
