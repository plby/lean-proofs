/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos882

def IsPrimitive (B : Finset ℕ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x ∣ y → x = y

def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  ((A.powerset.filter fun S ↦ S.Nonempty).image fun S ↦ ∑ a ∈ S, a)

noncomputable def maximumSize (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter fun A ↦
    IsPrimitive (nonemptySubsetSums A)).sup Finset.card

theorem erdos_882 (n : ℕ) (hn : 0 < n) :
    Real.logb 2 (n : ℝ) - 1 < (maximumSize n : ℝ) := by
  sorry

end Erdos882
