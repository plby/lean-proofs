import ErdosProblems.Erdos321.PrimeIntervalBounds
import ErdosProblems.Erdos321.FiniteRecurrence

namespace Erdos321

/-- For a positive quotient, `⌊N/p⌋=t` is exactly the usual reciprocal
interval `N/(t+1)<p≤N/t`. -/
theorem div_eq_iff_mem_quotient_interval
    {N p t : ℕ} (hp : 0 < p) (ht : 0 < t) :
    N / p = t ↔ N / (t + 1) < p ∧ p ≤ N / t := by
  constructor
  · intro hq
    have hlo : t * p ≤ N := (Nat.le_div_iff_mul_le hp).mp hq.ge
    have hhi : N < (t + 1) * p :=
      (Nat.div_lt_iff_lt_mul hp).mp (by omega : N / p < t + 1)
    constructor
    · rw [Nat.div_lt_iff_lt_mul (by omega : 0 < t + 1)]
      simpa [Nat.mul_comm] using hhi
    · rw [Nat.le_div_iff_mul_le ht]
      simpa [Nat.mul_comm] using hlo
  · rintro ⟨hlo, hhi⟩
    have hlo' : t * p ≤ N := by
      have := (Nat.le_div_iff_mul_le ht).mp hhi
      simpa [Nat.mul_comm] using this
    have hhi' : N < (t + 1) * p := by
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < t + 1)).mp hlo
      simpa [Nat.mul_comm] using this
    exact Nat.div_eq_of_lt_le hlo' hhi'

/-- Away from the cutoff boundary, the quotient-prime class is literally one
prime interval. -/
theorem quotientPrimes_eq_primeInterval
    {N Q t : ℕ} (ht : 0 < t) (hcut : Q < N / (t + 1)) :
    quotientPrimes N Q t = primeInterval (N / (t + 1)) (N / t) := by
  ext p
  constructor
  · intro hp
    have hpData := Finset.mem_filter.mp hp
    have hpBounds := Finset.mem_Icc.mp hpData.1
    have hpPrime := hpData.2.1
    have hpPos := hpPrime.pos
    have hInt := (div_eq_iff_mem_quotient_interval hpPos ht).mp hpData.2.2
    rw [primeInterval, Finset.mem_filter]
    exact ⟨Finset.mem_Ioc.mpr hInt, hpPrime⟩
  · intro hp
    have hpData := Finset.mem_filter.mp hp
    have hpInt := Finset.mem_Ioc.mp hpData.1
    have hpPrime := hpData.2
    have hpPos := hpPrime.pos
    have hq := (div_eq_iff_mem_quotient_interval hpPos ht).mpr hpInt
    rw [quotientPrimes, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hpPrime, hq⟩
    exact hpInt.2.trans (Nat.div_le_self N t)

/-- Uniform two-sided estimates for every interior quotient-prime class. -/
theorem exists_quotientPrime_bounds :
    ∃ C ≥ 0, ∀ {N Q t : ℕ}, 0 < t → Q < N / (t + 1) →
      2 ≤ N / (t + 1) →
      (quotientPrimes N Q t).card *
          Real.log ((N / (t + 1) : ℕ) : ℝ) ≤
        ((N / t : ℕ) : ℝ) - ((N / (t + 1) : ℕ) : ℝ) +
          C * ((N / t : ℕ) : ℝ) / Real.log ((N / t : ℕ) : ℝ) ^ 2 +
          C * ((N / (t + 1) : ℕ) : ℝ) /
            Real.log ((N / (t + 1) : ℕ) : ℝ) ^ 2 ∧
      ((N / t : ℕ) : ℝ) - ((N / (t + 1) : ℕ) : ℝ) -
          (C * ((N / t : ℕ) : ℝ) / Real.log ((N / t : ℕ) : ℝ) ^ 2 +
            C * ((N / (t + 1) : ℕ) : ℝ) /
              Real.log ((N / (t + 1) : ℕ) : ℝ) ^ 2) ≤
        (quotientPrimes N Q t).card * Real.log ((N / t : ℕ) : ℝ) := by
  obtain ⟨C, hC, hIntervals⟩ := exists_primeInterval_theta_bounds
  refine ⟨C, hC, ?_⟩
  intro N Q t ht hcut ha
  have hab : N / (t + 1) ≤ N / t :=
    Nat.div_le_div_left (by omega) ht
  rw [quotientPrimes_eq_primeInterval ht hcut]
  exact hIntervals ha hab

/-- Division form of the quotient-class estimates, ready for insertion into
the upper and lower recurrences. -/
theorem exists_quotientPrime_card_bounds :
    ∃ C ≥ 0, ∀ {N Q t : ℕ}, 0 < t → Q < N / (t + 1) →
      2 ≤ N / (t + 1) →
      (((N / t : ℕ) : ℝ) - ((N / (t + 1) : ℕ) : ℝ) -
          (C * ((N / t : ℕ) : ℝ) / Real.log ((N / t : ℕ) : ℝ) ^ 2 +
            C * ((N / (t + 1) : ℕ) : ℝ) /
              Real.log ((N / (t + 1) : ℕ) : ℝ) ^ 2)) /
            Real.log ((N / t : ℕ) : ℝ) ≤
        (quotientPrimes N Q t).card ∧
      (quotientPrimes N Q t).card ≤
        (((N / t : ℕ) : ℝ) - ((N / (t + 1) : ℕ) : ℝ) +
          C * ((N / t : ℕ) : ℝ) / Real.log ((N / t : ℕ) : ℝ) ^ 2 +
          C * ((N / (t + 1) : ℕ) : ℝ) /
            Real.log ((N / (t + 1) : ℕ) : ℝ) ^ 2) /
          Real.log ((N / (t + 1) : ℕ) : ℝ) := by
  obtain ⟨C, hC, hBounds⟩ := exists_quotientPrime_bounds
  refine ⟨C, hC, ?_⟩
  intro N Q t ht hcut ha
  have hb : 2 ≤ N / t := ha.trans (Nat.div_le_div_left (by omega) ht)
  have hlogA : 0 < Real.log ((N / (t + 1) : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two ha)
  have hlogB : 0 < Real.log ((N / t : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hb)
  have h := hBounds ht hcut ha
  constructor
  · exact (div_le_iff₀ hlogB).2 h.2
  · exact (le_div_iff₀ hlogA).2 h.1

end Erdos321
