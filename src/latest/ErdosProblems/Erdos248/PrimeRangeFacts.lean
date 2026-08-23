import ErdosProblems.Erdos248.PrimeRanges
import ErdosProblems.Erdos248.PrimeSumBounds

/-!
# Erdős Problem 248: elementary facts about the three prime ranges

This file packages the membership and separation consequences used by the
moment arguments.  In particular, the upper endpoint of `mediumPrimes` is
strict: on a near coordinate it is a nontrivial power of two and hence is
not prime.
-/

namespace Erdos248

/-! ## Medium primes -/

theorem prime_of_mem_mediumPrimes {K k p : ℕ}
    (hp : p ∈ mediumPrimes K k) : p.Prime :=
  (mem_primesBetween.mp hp).2.2

theorem tinyCutoff_lt_of_mem_mediumPrimes {K k p : ℕ}
    (hp : p ∈ mediumPrimes K k) : tinyCutoff K < p :=
  (mem_primesBetween.mp hp).1

/-- A medium prime is strictly below its coordinate radius.  Membership only
gives a weak upper bound, so the endpoint case is excluded using that the
near-coordinate radius is a power of two with exponent at least two. -/
theorem lt_shiftRadius_of_mem_mediumPrimes {K k p : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K) (hp : p ∈ mediumPrimes K k) :
    p < shiftRadius K k := by
  have hpData := mem_primesBetween.mp hp
  have hsub : 0 < 100 * K - k := by omega
  have hexp : 2 ≤ 100 ^ (100 * K - k) := by
    have hone : 1 < 100 ^ (100 * K - k) :=
      Nat.one_lt_pow hsub.ne' (by norm_num)
    omega
  have hnotPrime : ¬(shiftRadius K k).Prime := by
    rw [shiftRadius_eq_pow]
    exact Nat.Prime.not_prime_pow hexp
  have hne : p ≠ shiftRadius K k := by
    intro heq
    apply hnotPrime
    simpa [← heq] using hpData.2.2
  exact lt_of_le_of_ne hpData.2.1 hne

theorem mem_mediumPrimes_facts {K k p : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K) (hp : p ∈ mediumPrimes K k) :
    p.Prime ∧ tinyCutoff K < p ∧ p < shiftRadius K k :=
  ⟨prime_of_mem_mediumPrimes hp, tinyCutoff_lt_of_mem_mediumPrimes hp,
    lt_shiftRadius_of_mem_mediumPrimes hk1 hkK hp⟩

/-! ## Large primes -/

theorem prime_of_mem_largePrimes {K k p : ℕ}
    (hp : p ∈ largePrimes K k) : p.Prime :=
  (mem_primesBetween.mp hp).2.2

theorem shiftRadius_lt_of_mem_largePrimes {K k p : ℕ}
    (hp : p ∈ largePrimes K k) : shiftRadius K k < p :=
  (mem_primesBetween.mp hp).1

theorem shiftRadius_le_of_mem_largePrimes {K k p : ℕ}
    (hp : p ∈ largePrimes K k) : shiftRadius K k ≤ p :=
  (shiftRadius_lt_of_mem_largePrimes hp).le

theorem tinyCutoff_lt_of_mem_largePrimes {K k p : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K) (hp : p ∈ largePrimes K k) :
    tinyCutoff K < p := by
  have hK : 0 < K := lt_of_lt_of_le (by omega : 0 < k) hkK
  exact (tinyCutoff_le_shiftRadius hK hkK).trans_lt
    (shiftRadius_lt_of_mem_largePrimes hp)

/-- Every large prime at a near coordinate exceeds the distance to every
near shift (including, harmlessly, the coordinate itself). -/
theorem largePrime_separated {K k p : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K) (hp : p ∈ largePrimes K k)
    (h : nearShifts K) :
    Nat.dist k h.1 < p := by
  have hcut := tinyCutoff_lt_of_mem_largePrimes hk1 hkK hp
  have hKp : K < p := (K_le_tinyCutoff K).trans_lt hcut
  have hhK := (mem_nearShifts.mp h.property).2
  unfold Nat.dist
  omega

theorem mem_largePrimes_facts {K k p : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K) (hp : p ∈ largePrimes K k) :
    p.Prime ∧ tinyCutoff K < p ∧ shiftRadius K k ≤ p :=
  ⟨prime_of_mem_largePrimes hp,
    tinyCutoff_lt_of_mem_largePrimes hk1 hkK hp,
    shiftRadius_le_of_mem_largePrimes hp⟩

/-! ## Far primes -/

theorem prime_of_mem_farPrimes {K k p : ℕ}
    (hp : p ∈ farPrimes K k) : p.Prime :=
  (mem_primesBetween.mp hp).2.2

theorem tinyCutoff_lt_of_mem_farPrimes {K k p : ℕ}
    (hp : p ∈ farPrimes K k) : tinyCutoff K < p := by
  exact (Nat.le_max_left (tinyCutoff K) k).trans_lt
    (mem_primesBetween.mp hp).1

theorem farShift_lt_of_mem_farPrimes {K k p : ℕ}
    (hp : p ∈ farPrimes K k) : k < p := by
  exact (Nat.le_max_right (tinyCutoff K) k).trans_lt
    (mem_primesBetween.mp hp).1

/-- A far-range prime exceeds the distance from the far shift to every near
coordinate. -/
theorem farPrime_separated {K k p : ℕ} (hKk : K < k)
    (hp : p ∈ farPrimes K k) (h : nearShifts K) :
    Nat.dist k h.1 < p := by
  have hkp := farShift_lt_of_mem_farPrimes hp
  have hhK := (mem_nearShifts.mp h.property).2
  unfold Nat.dist
  omega

theorem mem_farPrimes_facts {K k p : ℕ} (hKk : K < k)
    (hp : p ∈ farPrimes K k) :
    p.Prime ∧ tinyCutoff K < p ∧
      ∀ h : nearShifts K, Nat.dist k h.1 < p := by
  exact ⟨prime_of_mem_farPrimes hp, tinyCutoff_lt_of_mem_farPrimes hp,
    fun h => farPrime_separated hKk hp h⟩

end Erdos248
