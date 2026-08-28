/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Erdos1123.WeightedQuotient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Continuum

namespace Erdos1123

/-- Ordinary counting-density weights on positive initial segments. -/
noncomputable def ordinaryWeights : WeightSequence ℕ where
  support n := Finset.Icc 1 n
  weight n _ := (n : ℝ)⁻¹
  nonneg n _ := inv_nonneg.mpr (Nat.cast_nonneg n)

/-- Logarithmic-density weights on positive initial segments. -/
noncomputable def logarithmicWeights : WeightSequence ℕ where
  support n := Finset.Icc 1 n
  weight n x := (x : ℝ)⁻¹ / Real.log n
  nonneg n x := div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg x))
    (Real.log_natCast_nonneg n)

abbrev B₁ := ordinaryWeights.Algebra

abbrev B₂ := logarithmicWeights.Algebra

/-- Under the continuum hypothesis, the density quotient Boolean algebras
are order-isomorphic. -/
theorem erdos_1123
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1) :
    Nonempty (B₁ ≃o B₂) := by
  sorry

end Erdos1123
