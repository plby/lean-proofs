import ErdosProblems.Erdos1123.WeightedQuotient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# The two density algebras and the Continuum Hypothesis

Sets are subsets of `ℕ`; the density statistics use the positive integers
`1, ..., n`, so that membership of `0` has no effect on either quotient.
-/

namespace Erdos1123

open Filter
open scoped Topology symmDiff Classical

/-- CH, with no additional hypotheses hidden in the definition. -/
def ContinuumHypothesis : Prop := Cardinal.continuum.{0} = Cardinal.aleph 1

/-- Ordinary counting density on the positive initial segments. -/
noncomputable def ordinaryWeights : WeightSequence ℕ where
  support n := Finset.Icc 1 n
  weight n _ := (n : ℝ)⁻¹
  nonneg n _ := inv_nonneg.mpr (Nat.cast_nonneg n)

/-- Logarithmic density on the positive initial segments. Lean's conventions
`log 0 = 0` and `0⁻¹ = 0` only affect irrelevant initial terms. -/
noncomputable def logarithmicWeights : WeightSequence ℕ where
  support n := Finset.Icc 1 n
  weight n x := (x : ℝ)⁻¹ / Real.log n
  nonneg n x := div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg x))
    (Real.log_natCast_nonneg n)

/-- The standard ordinary density-zero predicate. -/
noncomputable def DensityZero (A : Set ℕ) : Prop := by
  classical
  exact Tendsto (fun n => ((Finset.Icc 1 n).filter (· ∈ A)).card / (n : ℝ))
    atTop (𝓝 0)

/-- The standard logarithmic density-zero predicate. -/
noncomputable def LogDensityZero (A : Set ℕ) : Prop := by
  classical
  exact Tendsto (fun n =>
    (∑ x ∈ (Finset.Icc 1 n).filter (· ∈ A), (x : ℝ)⁻¹) / Real.log n)
    atTop (𝓝 0)

theorem ordinary_mass (A : Set ℕ) (n : ℕ) :
    ordinaryWeights.mass A n =
      ((Finset.Icc 1 n).filter (· ∈ A)).card / (n : ℝ) := by
  classical
  simp [WeightSequence.mass, ordinaryWeights, ← Finset.sum_filter, div_eq_mul_inv]

theorem logarithmic_mass (A : Set ℕ) (n : ℕ) :
    logarithmicWeights.mass A n =
      (∑ x ∈ (Finset.Icc 1 n).filter (· ∈ A), (x : ℝ)⁻¹) / Real.log n := by
  classical
  simp [WeightSequence.mass, logarithmicWeights, ← Finset.sum_filter,
    Finset.sum_div]

theorem ordinary_isNull_iff (A : Set ℕ) : ordinaryWeights.IsNull A ↔ DensityZero A := by
  unfold WeightSequence.IsNull DensityZero
  rw [funext (ordinary_mass A)]

theorem logarithmic_isNull_iff (A : Set ℕ) :
    logarithmicWeights.IsNull A ↔ LogDensityZero A := by
  unfold WeightSequence.IsNull LogDensityZero
  rw [funext (logarithmic_mass A)]

/-- Sets modulo ordinary density zero, equipped with their Boolean algebra. -/
abbrev B₁ := ordinaryWeights.Algebra

/-- Sets modulo logarithmic density zero, equipped with their Boolean algebra. -/
abbrev B₂ := logarithmicWeights.Algebra

theorem ordinary_quotient_eq_iff (A B : Set ℕ) :
    ordinaryWeights.quotientMap A = ordinaryWeights.quotientMap B ↔ DensityZero (A ∆ B) :=
  (ordinaryWeights.quotientMap_eq_iff A B).trans (ordinary_isNull_iff _)

theorem logarithmic_quotient_eq_iff (A B : Set ℕ) :
    logarithmicWeights.quotientMap A = logarithmicWeights.quotientMap B ↔
      LogDensityZero (A ∆ B) :=
  (logarithmicWeights.quotientMap_eq_iff A B).trans (logarithmic_isNull_iff _)

end Erdos1123
