import ErdosProblems.Erdos980.Basic
import ErdosProblems.Erdos980.ElliottTail.LargeTail

/-!
# Exact weighted-tail counting functions for Erdős Problem 980

These definitions use the strict prime cutoff from the problem.  The last
theorems give the literal medium/large partition used by Elliott's
uniform-integrability argument.
-/

namespace Erdos980.ElliottTail

open scoped BigOperators

/-- Rational primes strictly below `x`. -/
def primesBelow (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter Nat.Prime

/-- The exceptional prime set underlying the weighted tail. -/
noncomputable def exceptionalPrimes (k y x : ℕ) : Finset ℕ :=
  (primesBelow x).filter (fun p ↦ y < leastKthPowerNonresidue k p)

/-- The unnormalized contribution of least nonresidues exceeding `y`. -/
noncomputable def weightedTailSum (k y x : ℕ) : ℝ :=
  ∑ p ∈ exceptionalPrimes k y x,
    (leastKthPowerNonresidue k p : ℝ)

/-- The part of the tail in the interval `(y, Y]`. -/
noncomputable def mediumWeightedTailSum (k y Y x : ℕ) : ℝ :=
  ∑ p ∈ (primesBelow x).filter
      (fun p ↦ y < leastKthPowerNonresidue k p ∧
        leastKthPowerNonresidue k p ≤ Y),
    (leastKthPowerNonresidue k p : ℝ)

/-- Elliott's normalized tail. -/
noncomputable def normalizedWeightedTail (k y x : ℕ) : ℝ :=
  Real.log (x : ℝ) / (x : ℝ) * weightedTailSum k y x

/-- Elliott's normalized medium tail. -/
noncomputable def normalizedMediumWeightedTail (k y Y x : ℕ) : ℝ :=
  Real.log (x : ℝ) / (x : ℝ) * mediumWeightedTailSum k y Y x

theorem weightedTailSum_nonneg (k y x : ℕ) :
    0 ≤ weightedTailSum k y x := by
  unfold weightedTailSum
  positivity

@[simp] theorem mem_exceptionalPrimes {k y x p : ℕ} :
    p ∈ exceptionalPrimes k y x ↔
      p < x ∧ p.Prime ∧ y < leastKthPowerNonresidue k p := by
  simp [exceptionalPrimes, primesBelow, and_assoc]

/-- With `k ≥ 2`, membership in the positive tail forces Elliott
eligibility; all ineligible primes have value zero by definition. -/
theorem eligible_of_mem_exceptionalPrimes {k y x p : ℕ} (hk : 2 ≤ k)
    (hp : p ∈ exceptionalPrimes k y x) : Eligible k p := by
  have hpos : 0 < leastKthPowerNonresidue k p :=
    (Nat.zero_le y).trans_lt (mem_exceptionalPrimes.mp hp).2.2
  by_contra helig
  have hzero := leastKthPowerNonresidue_eq_zero_of_not_eligible
    (k := k) (p := p) (by tauto)
  omega

theorem mediumWeightedTailSum_nonneg (k y Y x : ℕ) :
    0 ≤ mediumWeightedTailSum k y Y x := by
  unfold mediumWeightedTailSum
  positivity

/-- Exact partition of the tail at a second cutoff `Y`. -/
theorem weightedTailSum_eq_medium_add_large
    (k y Y x : ℕ) (hyY : y ≤ Y) :
    weightedTailSum k y x =
      mediumWeightedTailSum k y Y x + weightedTailSum k Y x := by
  classical
  let s := (primesBelow x).filter
    (fun p ↦ y < leastKthPowerNonresidue k p)
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun p ↦ leastKthPowerNonresidue k p ≤ Y)
    (fun p ↦ (leastKthPowerNonresidue k p : ℝ))
  simpa only [weightedTailSum, exceptionalPrimes, mediumWeightedTailSum, s,
    Finset.filter_filter, not_le, and_assoc,
    and_iff_right_of_imp (fun h ↦ hyY.trans_lt h)] using hsplit.symm

/-- The exact normalized medium/large partition. -/
theorem normalizedWeightedTail_eq_medium_add_large
    (k y Y x : ℕ) (hyY : y ≤ Y) :
    normalizedWeightedTail k y x =
      normalizedMediumWeightedTail k y Y x +
        normalizedWeightedTail k Y x := by
  unfold normalizedWeightedTail normalizedMediumWeightedTail
  rw [weightedTailSum_eq_medium_add_large k y Y x hyY]
  ring

theorem normalizedWeightedTail_nonneg
    (k y x : ℕ) (hx : 2 ≤ x) :
    0 ≤ normalizedWeightedTail k y x := by
  apply mul_nonneg
  · apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ x by omega)
    · positivity
  · exact weightedTailSum_nonneg k y x

/-- Concrete combination of a cardinal rarity estimate and a pointwise
least-nonresidue estimate for one moving cutoff. -/
theorem normalizedWeightedTail_le_rpow
    (k y x : ℕ) (C D a b : ℝ) (hx : 2 ≤ x)
    (hcard : ((exceptionalPrimes k y x).card : ℝ) ≤ C * (x : ℝ) ^ a)
    (hpoint : ∀ p ∈ exceptionalPrimes k y x,
      (leastKthPowerNonresidue k p : ℝ) ≤ D * (x : ℝ) ^ b)
    (hD : 0 ≤ D) :
    normalizedWeightedTail k y x ≤
      C * D * (x : ℝ) ^ (a + b) * Real.log (x : ℝ) / (x : ℝ) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by omega) hx)
  have hmass : weightedTailSum k y x ≤
      C * D * (x : ℝ) ^ (a + b) := by
    unfold weightedTailSum
    exact exceptionalWeightedMass_le_rpow_add
      (exceptionalPrimes k y x)
      (fun p ↦ (leastKthPowerNonresidue k p : ℝ))
      C D x a b (fun _ _ ↦ by positivity) hcard hpoint hD hxpos
  unfold normalizedWeightedTail
  have hnorm : 0 ≤ Real.log (x : ℝ) / (x : ℝ) := by
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
    · positivity
  calc
    Real.log (x : ℝ) / (x : ℝ) * weightedTailSum k y x ≤
        Real.log (x : ℝ) / (x : ℝ) *
          (C * D * (x : ℝ) ^ (a + b)) :=
      mul_le_mul_of_nonneg_left hmass hnorm
    _ = C * D * (x : ℝ) ^ (a + b) * Real.log (x : ℝ) / (x : ℝ) := by
      ring

end Erdos980.ElliottTail
