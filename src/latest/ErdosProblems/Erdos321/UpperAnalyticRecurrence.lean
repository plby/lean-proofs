import ErdosProblems.Erdos321.AnalyticRecurrence
import ErdosProblems.Erdos321.EntropyRecurrence

namespace Erdos321

/-- A quotient class with a prime cutoff is exactly the reciprocal interval
with its lower endpoint truncated by that cutoff. -/
theorem quotientPrimes_eq_cutoffPrimeInterval
    {N Q t : ℕ} (ht : 0 < t) (htU : t ≤ N / (Q + 1)) :
    quotientPrimes N Q t =
      primeInterval (max Q (N / (t + 1))) (N / t) := by
  have hQb : Q < N / t := by
    have hmul : t * (Q + 1) ≤ N :=
      (Nat.le_div_iff_mul_le (by omega : 0 < Q + 1)).mp htU
    have : Q + 1 ≤ N / t := by
      rw [Nat.le_div_iff_mul_le ht]
      simpa [Nat.mul_comm] using hmul
    omega
  ext p
  constructor
  · intro hp
    have hpData := Finset.mem_filter.mp hp
    have hpBounds := Finset.mem_Icc.mp hpData.1
    have hpPrime := hpData.2.1
    have hInt := (div_eq_iff_mem_quotient_interval hpPrime.pos ht).mp hpData.2.2
    rw [primeInterval, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by exact max_lt hpBounds.1 hInt.1, hInt.2⟩, hpPrime⟩
  · intro hp
    have hpData := Finset.mem_filter.mp hp
    have hpInt := Finset.mem_Ioc.mp hpData.1
    have hpPrime := hpData.2
    have hLowerQ : Q < p := (lt_of_le_of_lt (le_max_left _ _) hpInt.1)
    have hLowerA : N / (t + 1) < p :=
      lt_of_le_of_lt (le_max_right _ _) hpInt.1
    have hq := (div_eq_iff_mem_quotient_interval hpPrime.pos ht).mpr
      ⟨hLowerA, hpInt.2⟩
    rw [quotientPrimes, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨by omega,
      hpInt.2.trans (Nat.div_le_self N t)⟩, hpPrime, hq⟩

/-- PNT upper coefficient after accounting for the upper recurrence's cutoff. -/
noncomputable def cutoffQuotientUpperCoefficient
    (C : ℝ) (N Q t : ℕ) : ℝ :=
  let a : ℝ := ((max Q (N / (t + 1)) : ℕ) : ℝ)
  let b : ℝ := ((N / t : ℕ) : ℝ)
  ((b - a) + (C * b / Real.log b ^ 2 + C * a / Real.log a ^ 2)) /
    Real.log a

/-- Uniform upper bounds for all quotient classes present in F-035, including
the cutoff-boundary class. -/
theorem exists_cutoffQuotientPrime_upper_bounds :
    ∃ C ≥ 0, ∀ {N Q t : ℕ}, 2 ≤ Q → 0 < t → t ≤ N / (Q + 1) →
      (quotientPrimes N Q t).card ≤ cutoffQuotientUpperCoefficient C N Q t := by
  obtain ⟨C, hC, hIntervals⟩ := exists_primeInterval_theta_bounds
  refine ⟨C, hC, ?_⟩
  intro N Q t hQ ht htU
  let a := max Q (N / (t + 1))
  let b := N / t
  have hQb : Q ≤ b := by
    have hmul : t * (Q + 1) ≤ N :=
      (Nat.le_div_iff_mul_le (by omega : 0 < Q + 1)).mp htU
    have : Q + 1 ≤ N / t := by
      rw [Nat.le_div_iff_mul_le ht]
      simpa [Nat.mul_comm] using hmul
    omega
  have hab0 : N / (t + 1) ≤ b := Nat.div_le_div_left (by omega) ht
  have hab : a ≤ b := max_le hQb hab0
  have ha : 2 ≤ a := hQ.trans (le_max_left _ _)
  have h := (hIntervals ha hab).1
  rw [quotientPrimes_eq_cutoffPrimeInterval ht htU]
  have hdiv := (le_div_iff₀ (Real.log_pos (by exact_mod_cast
    (lt_of_lt_of_le Nat.one_lt_two ha)))).2 h
  simpa [cutoffQuotientUpperCoefficient, a, b, add_assoc] using hdiv

/-- Fully analytic real upper recurrence, with no prime sets in its summand. -/
theorem exists_analytic_upper_recurrence_constant :
    ∃ C ≥ 0, ∀ {N Q : ℕ}, N < (Q + 1) * (Q + 1) →
      Q ≤ N → 2 ≤ Q → 1 ≤ N →
      harmonicEntropy N ≤
        Real.log (N + 1) +
          (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
            2 * Real.sqrt N * Real.log N) +
          ∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
            cutoffQuotientUpperCoefficient C N Q t * harmonicEntropy t := by
  obtain ⟨C, hC, hCard⟩ := exists_cutoffQuotientPrime_upper_bounds
  refine ⟨C, hC, ?_⟩
  intro N Q hUnique hQN hQ hN
  have hRec := harmonicEntropy_le_explicit_quotientRecurrence
    hUnique hQN (by omega) hN
  calc
    harmonicEntropy N ≤
        Real.log (N + 1) +
          (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
            2 * Real.sqrt N * Real.log N) +
          ∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
            (quotientPrimes N Q t).card * harmonicEntropy t := hRec
    _ ≤ _ := by
      have hSum :
          (∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
            (quotientPrimes N Q t).card * harmonicEntropy t) ≤
          ∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
            cutoffQuotientUpperCoefficient C N Q t * harmonicEntropy t := by
        apply Finset.sum_le_sum
        intro t ht
        have htData := Finset.mem_Icc.mp ht
        exact mul_le_mul_of_nonneg_right
          (hCard hQ htData.1 htData.2) (harmonicEntropy_nonneg t)
      linarith

/-- Even at the cutoff boundary, a quotient class is contained in its full
reciprocal prime interval. -/
theorem quotientPrimes_subset_primeInterval
    {N Q t : ℕ} (ht : 0 < t) :
    quotientPrimes N Q t ⊆ primeInterval (N / (t + 1)) (N / t) := by
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpPrime := hpData.2.1
  have hInt := (div_eq_iff_mem_quotient_interval hpPrime.pos ht).mp hpData.2.2
  rw [primeInterval, Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨hInt, hpPrime⟩

/-- Uniform full-interval upper coefficient, valid for every cutoff class. -/
theorem exists_fullQuotientPrime_upper_bounds :
    ∃ C ≥ 0, ∀ {N Q t : ℕ}, 0 < t → 2 ≤ N / (t + 1) →
      (quotientPrimes N Q t).card ≤ quotientUpperCoefficient C N t := by
  obtain ⟨C, hC, hIntervals⟩ := exists_primeInterval_theta_bounds
  refine ⟨C, hC, ?_⟩
  intro N Q t ht ha
  have hab : N / (t + 1) ≤ N / t :=
    Nat.div_le_div_left (by omega) ht
  have hcard : (quotientPrimes N Q t).card ≤
      (primeInterval (N / (t + 1)) (N / t)).card :=
    Finset.card_le_card (quotientPrimes_subset_primeInterval ht)
  have h := (hIntervals ha hab).1
  have hdiv := (le_div_iff₀ (Real.log_pos (by exact_mod_cast
    (lt_of_lt_of_le Nat.one_lt_two ha)))).2 h
  have hcardR : ((quotientPrimes N Q t).card : ℝ) ≤
      (primeInterval (N / (t + 1)) (N / t)).card := by
    exact_mod_cast hcard
  exact hcardR.trans (by
    simpa [quotientUpperCoefficient, add_assoc] using hdiv)

/-- Upper recurrence using the same untruncated analytic coefficient as the
lower recurrence, under one explicit final-endpoint hypothesis. -/
theorem exists_commonKernel_upper_recurrence_constant :
    ∃ C ≥ 0, ∀ {N Q : ℕ}, N < (Q + 1) * (Q + 1) →
      Q ≤ N → 1 ≤ Q → 1 ≤ N →
      2 ≤ N / (N / (Q + 1) + 1) →
      harmonicEntropy N ≤
        Real.log (N + 1) +
          (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
            2 * Real.sqrt N * Real.log N) +
          ∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
            quotientUpperCoefficient C N t * harmonicEntropy t := by
  obtain ⟨C, hC, hCard⟩ := exists_fullQuotientPrime_upper_bounds
  refine ⟨C, hC, ?_⟩
  intro N Q hUnique hQN hQ hN hEnd
  have hRec := harmonicEntropy_le_explicit_quotientRecurrence
    hUnique hQN hQ hN
  calc
    harmonicEntropy N ≤
        Real.log (N + 1) +
          (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
            2 * Real.sqrt N * Real.log N) +
          ∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
            (quotientPrimes N Q t).card * harmonicEntropy t := hRec
    _ ≤ _ := by
      have hSum :
          (∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
            (quotientPrimes N Q t).card * harmonicEntropy t) ≤
          ∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
            quotientUpperCoefficient C N t * harmonicEntropy t := by
        apply Finset.sum_le_sum
        intro t ht
        have htData := Finset.mem_Icc.mp ht
        have hden : N / (N / (Q + 1) + 1) ≤ N / (t + 1) :=
          Nat.div_le_div_left (Nat.add_le_add_right htData.2 1) (by omega)
        exact mul_le_mul_of_nonneg_right
          (hCard htData.1 (hEnd.trans hden)) (harmonicEntropy_nonneg t)
      linarith

end Erdos321
