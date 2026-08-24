/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset

namespace UnitFractions

variable (A : Set ℕ)

open scoped Classical in
noncomputable def partial_density (A : Set ℕ) (N : ℕ) : ℝ := ((range N).filter fun n ↦ n ∈ A).card / N

noncomputable def upper_density (A : Set ℕ) : ℝ := limsup (partial_density A) atTop

noncomputable def lower_density (A : Set ℕ) : ℝ := liminf (partial_density A) atTop

def has_density (A : Set ℕ) (d : ℝ) : Prop := upper_density A = d ∧ lower_density A = d

variable {A}

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos292

def IsLargestDenominator (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ UnitFractions.rec_sum S = 1

def largestDenominators : Set ℕ := {n | IsLargestDenominator n}

theorem erdos_292 : UnitFractions.has_density largestDenominators 1 := by
  sorry

end Erdos292
