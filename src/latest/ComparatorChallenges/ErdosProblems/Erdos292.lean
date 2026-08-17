import Mathlib

open Filter Finset Set

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace UnitFractions

variable (A : Set ℕ)

def partial_density (A : Set ℕ) (N : ℕ) : ℝ := ((range N).filter fun n ↦ n ∈ A).card / N

end UnitFractions

namespace UnitFractions

def upper_density (A : Set ℕ) : ℝ := limsup (partial_density A) atTop

end UnitFractions

namespace UnitFractions

def lower_density (A : Set ℕ) : ℝ := liminf (partial_density A) atTop

end UnitFractions

namespace UnitFractions

def has_density (A : Set ℕ) (d : ℝ) : Prop := upper_density A = d ∧ lower_density A = d

variable {A}

end UnitFractions

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos292

open UnitFractions

def IsLargestDenominator (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ rec_sum S = 1

end Erdos292

namespace Erdos292

def largestDenominators : Set ℕ := {n | IsLargestDenominator n}

end Erdos292

namespace Erdos292

open UnitFractions

theorem erdos292 : has_density largestDenominators 1 := by
  sorry

end Erdos292

end
