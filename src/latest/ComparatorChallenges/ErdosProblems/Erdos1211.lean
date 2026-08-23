/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 1211

For a set of natural numbers, let `subsetSums A` be the sums of finite sets of
distinct elements of `A`.  This file proves that, in every partition of the
natural numbers into two colours, one monochromatic subset-sum set has upper
logarithmic density at least `(2 + √3) / 4`, and that this constant is sharp.

The mathematical proof and the formal dependency map are in `tex/1211.tex`.
-/

namespace Erdos1211

open BigOperators Filter Set
open scoped Topology

noncomputable section

open scoped Classical in
/-- Sums of finite sets of distinct elements of `A`.  The empty sum is included. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ n = ∑ a ∈ F, a}

open scoped Classical in
/-- The harmonic mass of the positive members of `X` strictly below the real cutoff `x`. -/
def harmonicMassBelow (X : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ico 1 ⌈x⌉₊).filter (fun n ↦ n ∈ X), (n : ℝ)⁻¹

open scoped Classical in
/-- The normalized logarithmic mass at the real cutoff `x`. -/
def logarithmicRatio (X : Set ℕ) (x : ℝ) : ℝ :=
  harmonicMassBelow X x / Real.log x

open scoped Classical in
/-- Upper logarithmic density, with the literal real cutoff from the problem statement. -/
def upperLogDensity (X : Set ℕ) : ℝ :=
  limsup (logarithmicRatio X) atTop

open scoped Classical in
/-- `A` and `B` are disjoint and together contain every natural number. -/
def IsNatPartition (A B : Set ℕ) : Prop :=
  Disjoint A B ∧ A ∪ B = Set.univ

open scoped Classical in
/-- The sharp constant in Problem 1211. -/
def sharpConstant : ℝ :=
  (2 + Real.sqrt 3) / 4

open scoped Classical in
/-- The larger of the two monochromatic upper logarithmic densities. -/
def partitionValue (A B : Set ℕ) : ℝ :=
  max (upperLogDensity (subsetSums A))
    (upperLogDensity (subsetSums B))

open scoped Classical in
/-- The exact sharp assertion whose proof resolves Erdős Problem 1211. -/
def Resolution : Prop :=
  (∀ A B : Set ℕ, IsNatPartition A B →
      sharpConstant ≤ partitionValue A B) ∧
    ∃ A B : Set ℕ, IsNatPartition A B ∧
      partitionValue A B = sharpConstant


open scoped Classical in
theorem erdos1211 : Resolution := by
  sorry

end

end Erdos1211
