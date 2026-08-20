import ErdosProblems.Erdos980.Model
import ErdosProblems.Erdos980.ElliottTail.Definitions

/-!
# The exact bridge from Elliott's weighted tail to the prime-value model

The abstract assembly theorem deletes the first `M` values in the increasing
enumeration of rational primes.  Elliott's estimates instead use a numerical
cutoff.  This file proves that these are literally the same tail: the cutoff
corresponding to `M` is `rationalPrime M - 1`.
-/

namespace Erdos980.ElliottTail

open Filter
open scoped BigOperators

noncomputable section

private theorem patternPiece_eq_sum_ite
    {k : ℕ} (hk : 2 ≤ k) (j x : ℕ) :
    (leastNonresidueModel k hk).enumeration j *
        primePatternCount (leastNonresidueModel k hk) j x =
      ∑ p ∈ primesBelow x,
        if leastKthPowerNonresidueLevel k p = some j then
          (leastKthPowerNonresidue k p : ℝ)
        else 0 := by
  rw [leastKthPowerNonresidueModel_enumeration,
    primePatternCount_leastKthPowerNonresidueModel hk]
  let s := (Finset.range x).filter
    (fun p ↦ p.Prime ∧ leastKthPowerNonresidue k p = rationalPrime j)
  change (rationalPrime j : ℝ) * (s.card : ℝ) = _
  calc
    (rationalPrime j : ℝ) * (s.card : ℝ) =
        ∑ _p ∈ s, (rationalPrime j : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]
    _ = ∑ p ∈ s, (leastKthPowerNonresidue k p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.2.symm
    _ = ∑ p ∈ primesBelow x,
          if leastKthPowerNonresidueLevel k p = some j then
            (leastKthPowerNonresidue k p : ℝ)
          else 0 := by
      classical
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext p
        simp only [s, primesBelow, Finset.mem_filter, Finset.mem_range]
        rw [leastKthPowerNonresidueLevel_eq_some_iff hk]
        tauto
      · intro p hp
        rfl

private theorem sum_levels_sub_eq_ite
    {k M p : ℕ} (hk : 2 ≤ k) :
    (leastKthPowerNonresidue k p : ℝ) -
        (∑ j ∈ Finset.range M,
          (if leastKthPowerNonresidueLevel k p = some j then
            (leastKthPowerNonresidue k p : ℝ)
          else 0)) =
      if rationalPrime M - 1 < leastKthPowerNonresidue k p then
        (leastKthPowerNonresidue k p : ℝ)
      else 0 := by
  classical
  let n := leastKthPowerNonresidue k p
  change (n : ℝ) -
      (∑ j ∈ Finset.range M,
        (if leastKthPowerNonresidueLevel k p = some j then (n : ℝ) else 0)) =
    if rationalPrime M - 1 < n then (n : ℝ) else 0
  by_cases hn : n = 0
  · simp [n, hn, leastKthPowerNonresidueLevel]
  · have hlevel : ∃ j, leastKthPowerNonresidueLevel k p = some j := by
      simp [leastKthPowerNonresidueLevel, n, hn]
    obtain ⟨j, hj⟩ := hlevel
    have hn_eq : n = rationalPrime j :=
      (leastKthPowerNonresidueLevel_eq_some_iff hk).mp hj
    have hthreshold :
        rationalPrime M - 1 < n ↔ M ≤ j := by
      rw [hn_eq]
      constructor
      · intro h
        by_contra hMj
        have hjM : j < M := Nat.lt_of_not_ge hMj
        have hrp : rationalPrime j < rationalPrime M :=
          rationalPrime_strictMono hjM
        omega
      · intro hMj
        have hrp : rationalPrime M ≤ rationalPrime j :=
          rationalPrime_strictMono.monotone hMj
        have hpos : 0 < rationalPrime M := rationalPrime_pos M
        omega
    by_cases hjM : j < M
    · have hnot : ¬ rationalPrime M - 1 < n := by
        rw [hthreshold]
        omega
      simp only [hnot, if_false]
      rw [sub_eq_zero]
      rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro i hi hij
        have hne : leastKthPowerNonresidueLevel k p ≠ some i := by
          intro hi'
          exact hij (Option.some.inj (hi'.symm.trans hj))
        simp [hne]
      · simp [hjM]
    · have htail : rationalPrime M - 1 < n := by
        rw [hthreshold]
        omega
      rw [if_pos htail, sub_eq_self]
      apply Finset.sum_eq_zero
      intro i hi
      have hiM : i < M := Finset.mem_range.mp hi
      have hne : leastKthPowerNonresidueLevel k p ≠ some i := by
        intro hi'
        have : i = j := Option.some.inj (hi'.symm.trans hj)
        omega
      simp [hne]

/-- Deleting the first `M` modeled prime values leaves exactly Elliott's
weighted tail above the numerical cutoff `rationalPrime M - 1`. -/
theorem primeValueTail_leastNonresidueModel_eq_weightedTailSum
    {k : ℕ} (hk : 2 ≤ k) (M x : ℕ) :
    primeValueTail (leastNonresidueModel k hk) M x =
      weightedTailSum k (rationalPrime M - 1) x := by
  classical
  rw [primeValueTail, primeValueSum_leastKthPowerNonresidueModel,
    primePatternHead]
  change
    (∑ p ∈ primesBelow x, (leastKthPowerNonresidue k p : ℝ)) -
        ∑ j ∈ Finset.range M,
          (leastNonresidueModel k hk).enumeration j *
            primePatternCount (leastNonresidueModel k hk) j x = _
  simp_rw [patternPiece_eq_sum_ite hk]
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  simp_rw [sum_levels_sub_eq_ite hk]
  rw [weightedTailSum, exceptionalPrimes, Finset.sum_filter]

/-- Division by the prime-number-theorem scale is exactly Elliott's
`log x / x` normalization. -/
theorem primeValueTail_div_erdos980Scale_eq_normalizedWeightedTail
    {k : ℕ} (hk : 2 ≤ k) (M x : ℕ) :
    primeValueTail (leastNonresidueModel k hk) M x / erdos980Scale x =
      normalizedWeightedTail k (rationalPrime M - 1) x := by
  rw [primeValueTail_leastNonresidueModel_eq_weightedTailSum hk]
  unfold erdos980Scale normalizedWeightedTail
  by_cases hx : x = 0
  · simp [hx]
  by_cases hlog : Real.log (x : ℝ) = 0
  · simp [hlog]
  field_simp

/-- Increasing the numerical cutoff can only remove nonnegative summands. -/
theorem weightedTailSum_antitone_cutoff (k x : ℕ) :
    Antitone (fun y ↦ weightedTailSum k y x) := by
  intro y Y hyY
  unfold weightedTailSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hp' := mem_exceptionalPrimes.mp hp
    exact mem_exceptionalPrimes.mpr
      ⟨hp'.1, hp'.2.1, hyY.trans_lt hp'.2.2⟩
  · intro p hp hmissing
    positivity

/-- The exact abstract model tail is antitone in the number of deleted
levels. -/
theorem primeValueTail_leastNonresidueModel_antitone
    {k : ℕ} (hk : 2 ≤ k) (x : ℕ) :
    Antitone (fun M ↦ primeValueTail (leastNonresidueModel k hk) M x) := by
  intro M N hMN
  change primeValueTail (leastNonresidueModel k hk) N x ≤
    primeValueTail (leastNonresidueModel k hk) M x
  rw [primeValueTail_leastNonresidueModel_eq_weightedTailSum hk,
    primeValueTail_leastNonresidueModel_eq_weightedTailSum hk]
  apply weightedTailSum_antitone_cutoff
  have hrp := rationalPrime_strictMono.monotone hMN
  omega

/-- A uniform smallness estimate for Elliott's exact normalized weighted
tails is precisely the uniform-integrability hypothesis required by the
abstract prime-value assembly theorem. -/
theorem uniformlyNegligibleTail_leastNonresidueModel_of_normalizedWeightedTail
    {k : ℕ} (hk : 2 ≤ k)
    (hsmall : ∀ ε > 0, ∃ M₀, ∀ M ≥ M₀,
      ∀ᶠ x : ℕ in atTop,
        normalizedWeightedTail k (rationalPrime M - 1) x < ε) :
    UniformlyNegligibleTail
      (primeValueTail (leastNonresidueModel k hk)) erdos980Scale := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hsmall ε hε
  refine ⟨M₀, fun M hM ↦ ?_⟩
  filter_upwards [hM₀ M hM, eventually_ge_atTop 2] with x hxsmall hx
  rw [primeValueTail_div_erdos980Scale_eq_normalizedWeightedTail hk]
  rw [abs_of_nonneg (normalizedWeightedTail_nonneg k
    (rationalPrime M - 1) x hx)]
  exact hxsmall

end

end Erdos980.ElliottTail
