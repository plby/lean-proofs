import ErdosProblems.Erdos327.Analytic.RoughCount

namespace Erdos327.Analytic

open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

/-- For a positive rough integer lying below the upper cutoff, the localized
factor count is its full factor count. -/
theorem primeFactorCountBetween_eq_cardFactors_of_rough
    {L X n : ℕ} (hn : 0 < n) (hnX : n ≤ X)
    (hrough : Rough L n) :
    primeFactorCountBetween L X n =
      ArithmeticFunction.cardFactors n := by
  unfold primeFactorCountBetween
  rw [ArithmeticFunction.cardFactors_apply]
  congr 1
  apply List.filter_eq_self.mpr
  intro p hpList
  have hpPrime := Nat.prime_of_mem_primeFactorsList hpList
  have hpDvd := Nat.dvd_of_mem_primeFactorsList hpList
  have hpL : L ≤ p := by
    by_contra hpNot
    exact hrough p hpPrime (Nat.lt_of_not_ge hpNot) hpDvd
  have hpN : p ≤ n := Nat.le_of_dvd hn hpDvd
  simpa using (show L ≤ p ∧ p ≤ X from ⟨hpL, hpN.trans hnX⟩)

/-- A localized factor count never exceeds the full factor count. -/
theorem primeFactorCountBetween_le_cardFactors
    (L X n : ℕ) :
    primeFactorCountBetween L X n ≤
      ArithmeticFunction.cardFactors n := by
  unfold primeFactorCountBetween
  rw [ArithmeticFunction.cardFactors_apply]
  exact List.length_filter_le _ _

/-- For a base in `[0,1]`, the full multiplicity weight is bounded by
every localized multiplicity weight. -/
theorem pow_cardFactors_le_pow_primeFactorCountBetween
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (L X n : ℕ) :
    q ^ ArithmeticFunction.cardFactors n ≤
      q ^ primeFactorCountBetween L X n :=
  pow_le_pow_of_le_one hq0 hq1
    (primeFactorCountBetween_le_cardFactors L X n)

/-- The number of distinct prime factors never exceeds the number of
prime factors counted with multiplicity. -/
theorem cardDistinctFactors_le_cardFactors (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n ≤
      ArithmeticFunction.cardFactors n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply,
    ArithmeticFunction.cardFactors_apply]
  exact n.primeFactorsList.dedup_sublist.length_le

/-- For a base in `[0,1]`, discarding repeated prime factors enlarges the
weight.  This is the pointwise reduction from the paper's `Ω` weights to
the finite sieve's squarefree (`ω`) weights. -/
theorem pow_cardFactors_le_pow_cardDistinctFactors
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    q ^ ArithmeticFunction.cardFactors n ≤
      q ^ ArithmeticFunction.cardDistinctFactors n :=
  pow_le_pow_of_le_one hq0 hq1 (cardDistinctFactors_le_cardFactors n)

end Erdos327.Analytic
