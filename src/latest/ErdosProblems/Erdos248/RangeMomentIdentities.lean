import ErdosProblems.Erdos248.BadMassAssembly
import ErdosProblems.Erdos248.MomentCombinatorics
import ErdosProblems.Erdos248.PrimeSumBounds
import ErdosProblems.Erdos248.EventMass

/-!
# Erdős Problem 248: prime-range counts as indicator moments

This file connects the arithmetic range counts used by the deterministic
reduction to the finite weighted-moment API.  It also identifies the abstract
weighted mass of a finite prime-product event with the concrete transformed
event mass used by the sieve estimates.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance rangeMomentIdentitiesDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Arithmetic counts as sums of divisibility indicators -/

/-- The number of prime divisors of `m` in `lo < p <= hi`, cast to the
reals, is the corresponding sum of divisibility indicators. -/
theorem omegaBetween_cast_eq_sum_realIndicator
    {m lo hi : ℕ} (hm : 0 < m) :
    (omegaBetween m lo hi : ℝ) =
      ∑ p ∈ primesBetween lo hi, realIndicator (p ∣ m) := by
  classical
  let S := m.primeFactors.filter fun p => lo < p ∧ p ≤ hi
  have hfilter :
      S = (primesBetween lo hi).filter fun p => p ∣ m := by
    ext p
    simp only [S, Finset.mem_filter, mem_primesBetween]
    constructor
    · rintro ⟨hpf, hlop, hphi⟩
      have hp := Nat.prime_of_mem_primeFactors hpf
      exact ⟨⟨hlop, hphi, hp⟩, Nat.dvd_of_mem_primeFactors hpf⟩
    · rintro ⟨⟨hlop, hphi, hp⟩, hpdiv⟩
      exact ⟨Nat.mem_primeFactors.mpr ⟨hp, hpdiv, hm.ne'⟩, hlop, hphi⟩
  change (S.card : ℝ) = _
  rw [hfilter, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hdiv : p ∣ m <;> simp [realIndicator, hdiv]

theorem mediumPrimeCount_cast_eq_indicatorSum
    {K k n : ℕ} (hnk : 0 < n + k) :
    (mediumPrimeCount K k n : ℝ) =
      ∑ p ∈ mediumPrimes K k, realIndicator (p ∣ n + k) := by
  simpa [mediumPrimeCount, mediumPrimes] using
    (omegaBetween_cast_eq_sum_realIndicator
      (m := n + k) (lo := tinyCutoff K) (hi := shiftRadius K k) hnk)

theorem largePrimeCount_cast_eq_largeIndicatorSum
    {K k n : ℕ} (hk : k ≤ K) (hnk : 0 < n + k) :
    (largePrimeCount K k n : ℝ) =
      ∑ p ∈ largePrimes K k, realIndicator (p ∣ n + k) := by
  simpa [largePrimeCount, largePrimes, largePrimeLower_of_le hk] using
    (omegaBetween_cast_eq_sum_realIndicator
      (m := n + k) (lo := shiftRadius K k) (hi := shiftRadius K 1) hnk)

theorem largePrimeCount_cast_eq_farIndicatorSum
    {K k n : ℕ} (hk : K < k) (hnk : 0 < n + k) :
    (largePrimeCount K k n : ℝ) =
      ∑ p ∈ farPrimes K k, realIndicator (p ∣ n + k) := by
  simpa [largePrimeCount, farPrimes, largePrimeLower_of_lt hk] using
    (omegaBetween_cast_eq_sum_realIndicator
      (m := n + k) (lo := max (tinyCutoff K) k)
        (hi := shiftRadius K 1) hnk)

/-! ## Weighted event-mass bridges -/

/-- The moment API's weighted mass of a finite conjunction of prime events is
exactly the concrete event mass used by the finite-prime transform. -/
theorem weightedMass_primeDivisibility_eq_primeProductEventMass
    (K k : ℕ) (P : Finset ℕ) :
    weightedMass (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K) (fun n => ∀ p ∈ P, p ∣ n + k) =
      primeProductEventMass K k P := by
  classical
  unfold weightedMass weightedSum primeProductEventMass sieveWeightSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : ∀ p ∈ P, p ∣ n + k <;> simp [realIndicator, h]

/-- `mediumPrimeBadMass` is literally a weighted mass in the moment API. -/
theorem mediumPrimeBadMass_eq_weightedMass (K T k : ℕ) :
    mediumPrimeBadMass K T k =
      weightedMass (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K) (fun n => T * k < mediumPrimeCount K k n) := by
  classical
  unfold mediumPrimeBadMass weightedMass weightedSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : T * k < mediumPrimeCount K k n <;>
    simp [realIndicator, h]

/-- `largePrimeBadMass` is literally a weighted mass in the moment API. -/
theorem largePrimeBadMass_eq_weightedMass (K T k : ℕ) :
    largePrimeBadMass K T k =
      weightedMass (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K) (fun n => T * k < largePrimeCount K k n) := by
  classical
  unfold largePrimeBadMass weightedMass weightedSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : T * k < largePrimeCount K k n <;>
    simp [realIndicator, h]

private theorem dyadic_point_add_pos {K n k : ℕ}
    (hn : n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K)) :
    0 < n + k := by
  have hnlow := (Finset.mem_Ico.mp hn).1
  exact (intervalStart_pos K).trans_le (hnlow.trans (Nat.le_add_right n k))

/-- Exact threshold-event form of the medium bad mass, ready for raw-moment
Markov with threshold `T*k+1`. -/
theorem mediumPrimeBadMass_eq_weightedMass_indicatorThreshold
    (K T k : ℕ) :
    mediumPrimeBadMass K T k =
      weightedMass (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K) (fun n =>
          (((T * k + 1 : ℕ) : ℝ) ≤
            |∑ p ∈ mediumPrimes K k, realIndicator (p ∣ n + k)|)) := by
  rw [mediumPrimeBadMass_eq_weightedMass]
  unfold weightedMass weightedSum
  apply Finset.sum_congr rfl
  intro n hn
  have hcount := mediumPrimeCount_cast_eq_indicatorSum (K := K) (k := k)
    (dyadic_point_add_pos (k := k) hn)
  have hevent :
      (T * k < mediumPrimeCount K k n) ↔
        (((T * k + 1 : ℕ) : ℝ) ≤
          |∑ p ∈ mediumPrimes K k, realIndicator (p ∣ n + k)|) := by
    rw [← hcount, abs_of_nonneg (by positivity)]
    norm_cast
  change sieveWeight K n * realIndicator (T * k < mediumPrimeCount K k n) =
    sieveWeight K n * realIndicator
      ((((T * k + 1 : ℕ) : ℝ) ≤
        |∑ p ∈ mediumPrimes K k, realIndicator (p ∣ n + k)|))
  rw [propext hevent]

/-- Near-shift version of the large-prime threshold event. -/
theorem largePrimeBadMass_eq_weightedMass_largeIndicatorThreshold
    {K T k : ℕ} (hk : k ≤ K) :
    largePrimeBadMass K T k =
      weightedMass (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K) (fun n =>
          (((T * k + 1 : ℕ) : ℝ) ≤
            |∑ p ∈ largePrimes K k, realIndicator (p ∣ n + k)|)) := by
  rw [largePrimeBadMass_eq_weightedMass]
  unfold weightedMass weightedSum
  apply Finset.sum_congr rfl
  intro n hn
  have hcount := largePrimeCount_cast_eq_largeIndicatorSum hk
    (dyadic_point_add_pos (k := k) hn)
  have hevent :
      (T * k < largePrimeCount K k n) ↔
        (((T * k + 1 : ℕ) : ℝ) ≤
          |∑ p ∈ largePrimes K k, realIndicator (p ∣ n + k)|) := by
    rw [← hcount, abs_of_nonneg (by positivity)]
    norm_cast
  change sieveWeight K n * realIndicator (T * k < largePrimeCount K k n) =
    sieveWeight K n * realIndicator
      ((((T * k + 1 : ℕ) : ℝ) ≤
        |∑ p ∈ largePrimes K k, realIndicator (p ∣ n + k)|))
  rw [propext hevent]

/-- Far-shift version of the large-prime threshold event. -/
theorem largePrimeBadMass_eq_weightedMass_farIndicatorThreshold
    {K T k : ℕ} (hk : K < k) :
    largePrimeBadMass K T k =
      weightedMass (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K) (fun n =>
          (((T * k + 1 : ℕ) : ℝ) ≤
            |∑ p ∈ farPrimes K k, realIndicator (p ∣ n + k)|)) := by
  rw [largePrimeBadMass_eq_weightedMass]
  unfold weightedMass weightedSum
  apply Finset.sum_congr rfl
  intro n hn
  have hcount := largePrimeCount_cast_eq_farIndicatorSum hk
    (dyadic_point_add_pos (k := k) hn)
  have hevent :
      (T * k < largePrimeCount K k n) ↔
        (((T * k + 1 : ℕ) : ℝ) ≤
          |∑ p ∈ farPrimes K k, realIndicator (p ∣ n + k)|) := by
    rw [← hcount, abs_of_nonneg (by positivity)]
    norm_cast
  change sieveWeight K n * realIndicator (T * k < largePrimeCount K k n) =
    sieveWeight K n * realIndicator
      ((((T * k + 1 : ℕ) : ℝ) ≤
        |∑ p ∈ farPrimes K k, realIndicator (p ∣ n + k)|))
  rw [propext hevent]

/-! ## Direct Markov interfaces -/

/-- The exact medium threshold bridge combined with square-moment Markov. -/
theorem threshold_sq_mul_mediumPrimeBadMass_le_secondMoment
    (K T k : ℕ) :
    (((T * k + 1 : ℕ) : ℝ) ^ 2) * mediumPrimeBadMass K T k ≤
      weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n => ∑ p ∈ mediumPrimes K k,
          realIndicator (p ∣ n + k)) := by
  rw [mediumPrimeBadMass_eq_weightedMass_indicatorThreshold]
  exact sq_mul_weightedMass_threshold_abs_le_secondMoment
    (by positivity) (fun n hn => sieveWeight_nonneg K n)

/-- Near large-prime square-moment Markov bound. -/
theorem threshold_sq_mul_largePrimeBadMass_le_secondMoment_near
    {K T k : ℕ} (hk : k ≤ K) :
    (((T * k + 1 : ℕ) : ℝ) ^ 2) * largePrimeBadMass K T k ≤
      weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n => ∑ p ∈ largePrimes K k,
          realIndicator (p ∣ n + k)) := by
  rw [largePrimeBadMass_eq_weightedMass_largeIndicatorThreshold hk]
  exact sq_mul_weightedMass_threshold_abs_le_secondMoment
    (by positivity) (fun n hn => sieveWeight_nonneg K n)

/-- Far large-prime square-moment Markov bound. -/
theorem threshold_sq_mul_largePrimeBadMass_le_secondMoment_far
    {K T k : ℕ} (hk : K < k) :
    (((T * k + 1 : ℕ) : ℝ) ^ 2) * largePrimeBadMass K T k ≤
      weightedSecondMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (fun n => ∑ p ∈ farPrimes K k,
          realIndicator (p ∣ n + k)) := by
  rw [largePrimeBadMass_eq_weightedMass_farIndicatorThreshold hk]
  exact sq_mul_weightedMass_threshold_abs_le_secondMoment
    (by positivity) (fun n hn => sieveWeight_nonneg K n)

end Erdos248
