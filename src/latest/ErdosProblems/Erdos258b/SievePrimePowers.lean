import ErdosProblems.Erdos258b.PrimePowerCounting
import ErdosProblems.Erdos248.Weight

/-!
# Prime-power estimates for the existing Problem 248 sieve

The pre-sieve modulus and every active CRT modulus are squarefree.  Therefore
the generic progression estimate applies to the existing weights without any
change to their construction or to the distinct-prime-factor estimates.
-/

open BoundedGaps.Maynard Erdos248
open scoped BigOperators

namespace Erdos258b

theorem squarefree_nat_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact max_le (ha.natFactorization_le_one p) (hb.natFactorization_le_one p)

theorem squarefree_divisorPairModulus {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hW : Squarefree W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) (hcross : IsCrossCoordinateCoprime H d e) :
    Squarefree (divisorPairModulus H W d e) := by
  classical
  have hcompat := isMaynardDivisorTuple_pair_lcm_compatible hd he hcross
  have hcop : Nat.Coprime W (∏ h : H, divisorTupleLcm H d e h) := by
    apply Nat.Coprime.prod_right
    intro h hh
    exact hcompat.1 h (by simp)
  apply (Nat.squarefree_mul hcop).mpr
  refine ⟨hW, Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_⟩
  · intro a ha b hb hab
    apply Nat.coprime_iff_isRelPrime.mp
    exact coprime_lcm_lcm_of_four (hd.coordinates_coprime hab)
      (hcross hab).1 (hcross hab).2 (he.coordinates_coprime hab)
  · intro h hh
    exact squarefree_nat_lcm (hd.coordinate_squarefree h) (he.coordinate_squarefree h)

noncomputable def sievePairSupport (K : ℕ) :
    Finset ((nearShifts K → ℕ) × (nearShifts K → ℕ)) := by
  classical
  exact ((sieveDivisorSupport K) ×ˢ (sieveDivisorSupport K)).filter
    fun de => IsCrossCoordinateCoprime (nearShifts K) de.1 de.2

noncomputable def sievePairResidue (K : ℕ)
    (de : (nearShifts K → ℕ) × (nearShifts K → ℕ)) : ℕ := by
  classical
  exact if h : de ∈ sievePairSupport K then
    divisorPairCrtResidue (nearShifts K) (globalRadius K) (preSieveModulus K) 0
      de.1 de.2
      (sieveDivisorSupport_isMaynard K de.1 (Finset.mem_product.mp
        (Finset.mem_filter.mp h).1).1)
      (sieveDivisorSupport_isMaynard K de.2 (Finset.mem_product.mp
        (Finset.mem_filter.mp h).1).2)
      (Finset.mem_filter.mp h).2
  else 0

theorem sievePairResidue_spec {K : ℕ}
    {de : (nearShifts K → ℕ) × (nearShifts K → ℕ)}
    (h : de ∈ sievePairSupport K) (n : ℕ) :
    n ≡ sievePairResidue K de [MOD divisorPairModulus (nearShifts K)
      (preSieveModulus K) de.1 de.2] ↔
      n ≡ 0 [MOD preSieveModulus K] ∧ divisorTuplePairCondition (nearShifts K) n de.1 de.2 := by
  classical
  rw [sievePairResidue, dif_pos h]
  exact modEq_divisorPairCrtResidue_iff _ _ (Finset.mem_filter.mp h).2 n

theorem sievePairModulus_squarefree {K : ℕ}
    {de : (nearShifts K → ℕ) × (nearShifts K → ℕ)}
    (h : de ∈ sievePairSupport K) :
    Squarefree (divisorPairModulus (nearShifts K) (preSieveModulus K) de.1 de.2) := by
  classical
  obtain ⟨hde, hcross⟩ := Finset.mem_filter.mp h
  obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
  exact squarefree_divisorPairModulus (squarefree_primorial _)
    (sieveDivisorSupport_isMaynard K _ hd) (sieveDivisorSupport_isMaynard K _ he) hcross

theorem sieveWeight_progression_expansion (K n : ℕ) :
    sieveWeight K n = ∑ de ∈ sievePairSupport K,
      if n ≡ sievePairResidue K de [MOD divisorPairModulus (nearShifts K)
        (preSieveModulus K) de.1 de.2]
      then sieveCoefficient K de.1 * sieveCoefficient K de.2 else 0 := by
  classical
  have hreplace : (∑ de ∈ sievePairSupport K,
      if n ≡ sievePairResidue K de [MOD divisorPairModulus (nearShifts K)
        (preSieveModulus K) de.1 de.2]
      then sieveCoefficient K de.1 * sieveCoefficient K de.2 else 0) =
      ∑ de ∈ sievePairSupport K,
        if n ≡ 0 [MOD preSieveModulus K] ∧
          divisorTuplePairCondition (nearShifts K) n de.1 de.2
        then sieveCoefficient K de.1 * sieveCoefficient K de.2 else 0 := by
    apply Finset.sum_congr rfl
    intro de hde
    exact if_congr (sievePairResidue_spec hde n) rfl rfl
  rw [hreplace, sieveWeight, preSievedSquareDivisorWeight_eq_pair_indicator]
  rw [sievePairSupport, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hcross : IsCrossCoordinateCoprime (nearShifts K) d e
  · simp [hcross]
  · have hnot : ¬divisorTuplePairCondition (nearShifts K) n d e := by
      intro hpair
      exact hcross (isCrossCoordinateCoprime_of_pairCondition
        (sieveDivisorSupport_isMaynard K d hd) (sieveDivisorSupport_isMaynard K e he)
        (nearShifts_cover K) hpair)
    simp [hcross, hnot]

theorem sievePair_abs_sum (K : ℕ) :
    (∑ de ∈ sievePairSupport K, |sieveCoefficient K de.1 * sieveCoefficient K de.2|) =
      compatibleDivisorPairCoefficientMass (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K) := by
  classical
  simp [sievePairSupport, compatibleDivisorPairCoefficientMass,
    Finset.sum_filter, Finset.sum_product]

theorem sieve_prime_pow_mass_le {K p j : ℕ} (k : ℕ)
    (hp : p.Prime) (hj : 0 < j) :
    divisorEventMass (intervalStart K) k (p ^ j) (sieveWeight K) ≤
      sieveMass K / p ^ (j - 1) +
        2 * compatibleDivisorPairCoefficientMass (nearShifts K)
          (sieveDivisorSupport K) (sieveCoefficient K) := by
  have h := divisorEventMass_prime_pow_le (sievePairSupport K)
    (fun de => sieveCoefficient K de.1 * sieveCoefficient K de.2)
    (fun de => divisorPairModulus (nearShifts K) (preSieveModulus K) de.1 de.2)
    (sievePairResidue K) (intervalStart K) k (sieveWeight_nonneg K)
    (sieveWeight_progression_expansion K) (fun de hde => sievePairModulus_squarefree hde) hp hj
  rw [sievePair_abs_sum] at h
  exact h

end Erdos258b
