/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos1211

/-- Sums of finite sets of distinct elements of `A`.  The empty sum is included. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ n = ∑ a ∈ F, a}

open scoped Classical in
/-- The harmonic mass of the positive members of `X` strictly below the real cutoff `x`. -/
noncomputable def harmonicMassBelow (X : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ico 1 ⌈x⌉₊).filter (fun n ↦ n ∈ X), (n : ℝ)⁻¹

/-- The normalized logarithmic mass at the real cutoff `x`. -/
noncomputable def logarithmicRatio (X : Set ℕ) (x : ℝ) : ℝ :=
  harmonicMassBelow X x / Real.log x

/-- Upper logarithmic density, with the literal real cutoff from the problem statement. -/
noncomputable def upperLogDensity (X : Set ℕ) : ℝ :=
  limsup (logarithmicRatio X) atTop

/-- `A` and `B` are disjoint and together contain every natural number. -/
def IsNatPartition (A B : Set ℕ) : Prop :=
  Disjoint A B ∧ A ∪ B = Set.univ

/-- The sharp constant in Problem 1211. -/
noncomputable def sharpConstant : ℝ :=
  (2 + Real.sqrt 3) / 4

/-- The larger of the two monochromatic upper logarithmic densities. -/
noncomputable def partitionValue (A B : Set ℕ) : ℝ :=
  max (upperLogDensity (subsetSums A))
    (upperLogDensity (subsetSums B))

theorem erdos_1211 :
    (∀ A B : Set ℕ, IsNatPartition A B →
        sharpConstant ≤ partitionValue A B) ∧
      ∃ A B : Set ℕ, IsNatPartition A B ∧
        partitionValue A B = sharpConstant := by
  sorry

end Erdos1211
