/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionDecomposition

/-!
# Removing affine collision primes from the normalization support

For a fixed auxiliary prime `q`, every cross-family collision in a compatible
normalization quadruple divides one of finitely many affine differences.  The
squarefree product of the prime divisors of those differences above the
ordinary primorial cutoff can therefore be inserted into the divisor-tuple
pre-sieve.  On this augmented support all cross-family gcds are one, so the
general CRT kernel is exactly its tensor base.

This device is useful only for the normalization, where `q` is fixed.  The
pinned prime average still requires the uniform auxiliary-matrix estimates.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance erdos4ExceptionalPreSieveDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Squarefree product of the exceptional affine primes beyond `w`. -/
def crossExceptionalRoughRadical
    (H : Finset ℕ) (m q w : ℕ) : ℕ :=
  ∏ p ∈ (crossExceptionalModulus H m q).primeFactors.filter (w < ·), p

theorem crossExceptionalRoughRadical_pos
    (H : Finset ℕ) (m q w : ℕ) :
    0 < crossExceptionalRoughRadical H m q w := by
  unfold crossExceptionalRoughRadical
  exact Finset.prod_pos fun p hp ↦
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem crossExceptionalRoughRadical_squarefree
    (H : Finset ℕ) (m q w : ℕ) :
    Squarefree (crossExceptionalRoughRadical H m q w) := by
  unfold crossExceptionalRoughRadical
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp r hr hpr
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1)).mpr hpr
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree

theorem crossExceptionalRoughRadical_coprime_primorial
    (H : Finset ℕ) (m q w : ℕ) :
    (crossExceptionalRoughRadical H m q w).Coprime (primorial w) := by
  apply Nat.Coprime.prod_left
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpPrime := Nat.prime_of_mem_primeFactors hpData.1
  rw [hpPrime.coprime_iff_not_dvd]
  intro hpW
  exact (not_le_of_gt hpData.2) (hpPrime.dvd_primorial_iff.mp hpW)

theorem prime_dvd_crossExceptionalRoughRadical
    {H : Finset ℕ} {m q w p : ℕ}
    (hm : 0 < m) (hq : q.Prime)
    (hpPrime : p.Prime) (hwp : w < p)
    (hp : p ∣ crossExceptionalModulus H m q) :
    p ∣ crossExceptionalRoughRadical H m q w := by
  unfold crossExceptionalRoughRadical
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter]
  exact ⟨Nat.mem_primeFactors.mpr
    ⟨hpPrime, hp, (crossExceptionalModulus_pos (m := m)
      (q := q) hm hq).ne'⟩, hwp⟩

/-- A compatible cross gcd is trivial after all its possible rough prime
divisors have been inserted into the first-family pre-sieve modulus. -/
theorem crossCoordinateGcdProduct_eq_one_of_exceptionalPreSieve
    {H : Finset ℕ} {RD RE m q w : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w * crossExceptionalRoughRadical H m q w))
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD
      (primorial w * crossExceptionalRoughRadical H m q w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD
      (primorial w * crossExceptionalRoughRadical H m q w) d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE
      ((primorial w * crossExceptionalRoughRadical H m q w) * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE
      ((primorial w * crossExceptionalRoughRadical H m q w) * m) e')
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    crossCoordinateGcdProduct H d e d' e' = 1 := by
  let P := crossExceptionalRoughRadical H m q w
  have hdiv := crossCoordinateGcdProduct_dvd_crossExceptionalModulus_standard
    hm hq hRDq hREq hcover hd hd' he he' hcompat
  have hcopDP : (BoundedGaps.Maynard.divisorTupleProduct H d).Coprime P := by
    exact Nat.Coprime.of_dvd_right (dvd_mul_left P (primorial w)) hd.2.1
  have hcopD'P : (BoundedGaps.Maynard.divisorTupleProduct H d').Coprime P := by
    exact Nat.Coprime.of_dvd_right (dvd_mul_left P (primorial w)) hd'.2.1
  have hcoverE : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      ((primorial w * P) * m) :=
    coversShiftDifferencePrimes_of_dvd
      (dvd_mul_right (primorial w * P) m) hcover
  have hmE : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left m (primorial w * P)) he.2.1.symm
  have hmE' : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left m (primorial w * P)) he'.2.1.symm
  have hqD : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q (primorial w * P))
      (prime_mul_modulus_coprime_tupleProduct hd hq hRDq)
  have hqD' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q (primorial w * P))
      (prime_mul_modulus_coprime_tupleProduct hd' hq hRDq)
  have hqE : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q ((primorial w * P) * m))
      (prime_mul_modulus_coprime_tupleProduct he hq hREq)
  have hqE' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q ((primorial w * P) * m))
      (prime_mul_modulus_coprime_tupleProduct he' hq hREq)
  obtain ⟨hDD, hEE⟩ := withinFamilyLcm_pairwise_of_coordinateCompatible
    hm hq.pos hd hd' he he' hcover hcoverE hmE hmE'
      hqD hqD' hqE hqE' hcompat
  have hrough := crossCoordinateGcdProduct_roughModulusData hd hd' hDD hEE
  by_contra hne
  obtain ⟨p, hpPrime, hpCross⟩ := Nat.exists_prime_and_dvd hne
  have hpFactor : p ∈ (crossCoordinateGcdProduct H d e d' e').primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpPrime, hpCross, hrough.1.ne'⟩
  have hwp : w < p :=
    cutoff_lt_prime_of_mem_crossCoordinateGcdProduct_primeFactors
      (
        ⟨hd.1, Nat.Coprime.of_dvd_right (dvd_mul_right (primorial w) P)
          hd.2.1, hd.2.2⟩)
      (⟨hd'.1, Nat.Coprime.of_dvd_right (dvd_mul_right (primorial w) P)
          hd'.2.1, hd'.2.2⟩) hpFactor
  have hpP : p ∣ P := prime_dvd_crossExceptionalRoughRadical hm hq hpPrime hwp
    (hpCross.trans hdiv)
  have hpD : p ∣ BoundedGaps.Maynard.divisorTupleProduct H d ∨
      p ∣ BoundedGaps.Maynard.divisorTupleProduct H d' := by
    unfold crossCoordinateGcdProduct at hpCross
    obtain ⟨b, _hb, hpb⟩ :=
      (hpPrime.prime.dvd_finsetProd_iff _).mp hpCross
    obtain ⟨a, _ha, hpa⟩ :=
      (hpPrime.prime.dvd_finsetProd_iff _).mp hpb
    have hpLcm := hpa.trans (Nat.gcd_dvd_left _ _)
    rcases hpPrime.dvd_lcm.mp hpLcm with hpd | hpd'
    · exact Or.inl (hpd.trans
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d a))
    · exact Or.inr (hpd'.trans
        (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d' a))
  rcases hpD with hpD | hpD
  · exact (hpPrime.coprime_iff_not_dvd.mp
      (hcopDP.coprime_dvd_left hpD)) hpP
  · exact (hpPrime.coprime_iff_not_dvd.mp
      (hcopD'P.coprime_dvd_left hpD)) hpP

/-- On the exceptional-prime augmented support, every compatible
normalization summand has no cross-family totient amplification. -/
theorem crossCoordinateTotientSumProduct_eq_one_of_exceptionalPreSieve
    {H : Finset ℕ} {RD RE m q w : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w * crossExceptionalRoughRadical H m q w))
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD
      (primorial w * crossExceptionalRoughRadical H m q w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD
      (primorial w * crossExceptionalRoughRadical H m q w) d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE
      ((primorial w * crossExceptionalRoughRadical H m q w) * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE
      ((primorial w * crossExceptionalRoughRadical H m q w) * m) e')
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    crossCoordinateTotientSumProduct H d e d' e' = 1 := by
  rw [crossCoordinateTotientSumProduct_eq_crossGcd,
    crossCoordinateGcdProduct_eq_one_of_exceptionalPreSieve hm hq hRDq hREq
      hcover hd hd' he he' hcompat]
  norm_num

/-- The entire compatible-amplification correction vanishes on the
exceptional-prime augmented support.  This is the kernel-level form of
`crossCoordinateTotientSumProduct_eq_one_of_exceptionalPreSieve`. -/
theorem doubledSelbergCompatibleAmplificationCorrection_eq_zero_of_exceptionalPreSieve
    (H : Finset ℕ) (RD RE m q w : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w * crossExceptionalRoughRadical H m q w)) :
    doubledSelbergCompatibleAmplificationCorrection H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD
          (primorial w * crossExceptionalRoughRadical H m q w))
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE
          ((primorial w * crossExceptionalRoughRadical H m q w) * m))
        lambda m q = 0 := by
  classical
  unfold doubledSelbergCompatibleAmplificationCorrection
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  apply Finset.sum_eq_zero
  intro d' hd'
  apply Finset.sum_eq_zero
  intro e' he'
  by_cases hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e'
  · rw [if_pos hcompat]
    have hcross := crossCoordinateGcdProduct_eq_one_of_exceptionalPreSieve
      hm hq hRDq hREq hcover
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd)
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd')
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he)
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he') hcompat
    rw [hcross]
    norm_num
  · rw [if_neg hcompat]

/-- Consequently the augmented normalization kernel is its tensor base
minus only the incompatible-removal tail. -/
theorem doubledSelbergCrossTotientKernel_eq_tensorBase_sub_incompatible_of_exceptionalPreSieve
    (H : Finset ℕ) (RD RE m q w : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H
      (primorial w * crossExceptionalRoughRadical H m q w)) :
    doubledSelbergCrossTotientKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD
          (primorial w * crossExceptionalRoughRadical H m q w))
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE
          ((primorial w * crossExceptionalRoughRadical H m q w) * m))
        lambda m q =
      doubledSelbergTensorBaseKernel H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD
            (primorial w * crossExceptionalRoughRadical H m q w))
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE
            ((primorial w * crossExceptionalRoughRadical H m q w) * m))
          lambda -
        doubledSelbergIncompatibleRemovalCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD
            (primorial w * crossExceptionalRoughRadical H m q w))
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE
            ((primorial w * crossExceptionalRoughRadical H m q w) * m))
          lambda m q := by
  rw [doubledSelbergCrossTotientKernel_eq_tensorBase_add_corrections_standard
    H RD RE (primorial w * crossExceptionalRoughRadical H m q w) m q
    lambda hm hq hRDq hREq hcover]
  rw [doubledSelbergCompatibleAmplificationCorrection_eq_zero_of_exceptionalPreSieve
    H RD RE m q w lambda hm hq hRDq hREq hcover]
  ring

end

end Erdos4b
