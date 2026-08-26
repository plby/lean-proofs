/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionTail

/-!
# Leading tensor term and the two cross-collision corrections

The arbitrary-overlap normalization kernel differs from the product of its
two ordinary Maynard quadratic forms in exactly two ways.  A compatible
cross-family collision amplifies a summand by the cross gcd, while an
incompatible collision removes the tensor-base summand altogether.  This
file records that split as an exact finite identity.

The distinction matters analytically: the first correction is supported on
exceptional affine primes; the second is the usual rough starred collision
tail.  They cannot be conflated by simply deleting all cross-family overlaps
from the coefficient support.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance erdos4GeneralCollisionDecompositionDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The two lcm families are internally pairwise coprime.  On ordinary
Maynard support this is the tensor-base compatibility predicate. -/
def WithinFamilyCrossCoordinateCoprime
    {H : Finset ℕ} (d e d' e' : H → ℕ) : Prop :=
  BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' ∧
    BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e'

/-- Full affine CRT compatibility implies the within-family tensor-base
predicate on the two standard supports. -/
theorem withinFamilyCrossCoordinateCoprime_of_coordinateCompatible
    {H : Finset ℕ} {RD RE W m q : ℕ} {d e d' e' : H → ℕ}
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e')
    (hcompat : LargeGapCoordinateCrtCompatible H m q d e d' e') :
    WithinFamilyCrossCoordinateCoprime d e d' e' := by
  have hcoverE : BoundedGaps.Maynard.CoversShiftDifferencePrimes H (W * m) :=
    coversShiftDifferencePrimes_of_dvd (dvd_mul_right W m) hcover
  have hmE : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left m W) he.2.1.symm
  have hmE' : m.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left m W) he'.2.1.symm
  have hqD : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q W)
      (prime_mul_modulus_coprime_tupleProduct hd hq hRDq)
  have hqD' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H d') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q W)
      (prime_mul_modulus_coprime_tupleProduct hd' hq hRDq)
  have hqE : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e) :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q (W * m))
      (prime_mul_modulus_coprime_tupleProduct he hq hREq)
  have hqE' : q.Coprime (BoundedGaps.Maynard.divisorTupleProduct H e') :=
    Nat.Coprime.of_dvd_left (dvd_mul_left q (W * m))
      (prime_mul_modulus_coprime_tupleProduct he' hq hREq)
  obtain ⟨hDD, hEE⟩ := withinFamilyLcm_pairwise_of_coordinateCompatible
    hm hq.pos hd hd' he he' hcover hcoverE hmE hmE'
      hqD hqD' hqE hqE' hcompat
  constructor
  · intro a b hab
    exact ⟨
      Nat.Coprime.of_dvd (Nat.dvd_lcm_left (d a) (d' a))
        (Nat.dvd_lcm_right (d b) (d' b)) (hDD hab),
      Nat.Coprime.of_dvd (Nat.dvd_lcm_right (d a) (d' a))
        (Nat.dvd_lcm_left (d b) (d' b)) (hDD hab)⟩
  · intro a b hab
    exact ⟨
      Nat.Coprime.of_dvd (Nat.dvd_lcm_left (e a) (e' a))
        (Nat.dvd_lcm_right (e b) (e' b)) (hEE hab),
      Nat.Coprime.of_dvd (Nat.dvd_lcm_right (e a) (e' a))
        (Nat.dvd_lcm_left (e b) (e' b)) (hEE hab)⟩

/-- The unrestricted tensor leading term, retaining only the ordinary
within-family compatibility conditions. -/
noncomputable def doubledSelbergTensorBaseKernel
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if WithinFamilyCrossCoordinateCoprime d e d' e' then
      lambda d e * lambda d' e' /
        ((firstLcmProduct H d d' : ℝ) *
          companionLcmProduct H e e')
    else 0

/-- Gain beyond the tensor base from compatible cross-family gcds. -/
noncomputable def doubledSelbergCompatibleAmplificationCorrection
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (m q : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if LargeGapCoordinateCrtCompatible H m q d e d' e' then
      lambda d e * lambda d' e' *
        ((crossCoordinateGcdProduct H d e d' e' : ℝ) - 1) /
          ((firstLcmProduct H d d' : ℝ) *
            companionLcmProduct H e e')
    else 0

/-- Tensor-base mass deleted because a cross-family affine congruence is
incompatible. -/
noncomputable def doubledSelbergIncompatibleRemovalCorrection
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (m q : ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    if WithinFamilyCrossCoordinateCoprime d e d' e' ∧
        ¬LargeGapCoordinateCrtCompatible H m q d e d' e' then
      lambda d e * lambda d' e' /
        ((firstLcmProduct H d d' : ℝ) *
          companionLcmProduct H e e')
    else 0

/-- Exact normal-kernel split into the tensor leading term, compatible gcd
amplification, and incompatible removal. -/
theorem doubledSelbergCrossTotientKernel_eq_tensorBase_add_corrections_standard
    (H : Finset ℕ) (RD RE W m q : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W) :
    doubledSelbergCrossTotientKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        lambda m q =
      doubledSelbergTensorBaseKernel H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda +
        doubledSelbergCompatibleAmplificationCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda m q -
        doubledSelbergIncompatibleRemovalCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          lambda m q := by
  classical
  unfold doubledSelbergCrossTotientKernel doubledSelbergTensorBaseKernel
    doubledSelbergCompatibleAmplificationCorrection
    doubledSelbergIncompatibleRemovalCorrection
  simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  apply Finset.sum_congr rfl
  intro d' hd'Mem
  apply Finset.sum_congr rfl
  intro e' he'Mem
  let hd := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hdMem
  let hd' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd'Mem
  let he := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support heMem
  let he' := BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support he'Mem
  by_cases hc : LargeGapCoordinateCrtCompatible H m q d e d' e'
  · have hwithin :=
      withinFamilyCrossCoordinateCoprime_of_coordinateCompatible
        hm hq hRDq hREq hcover hd hd' he he' hc
    simp only [hc, hwithin, true_and, not_true_eq_false, if_true, if_false]
    rw [crossCoordinateTotientSumProduct_eq_crossGcd]
    ring
  · by_cases hwithin : WithinFamilyCrossCoordinateCoprime d e d' e'
    · simp [hc, hwithin]
    · simp [hc, hwithin]

/-- For a tensor coefficient, the leading kernel factors exactly into the
two ordinary compatible Maynard quadratic forms. -/
theorem doubledSelbergTensorBaseKernel_tensor
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambdaD lambdaE : (H → ℕ) → ℝ) :
    doubledSelbergTensorBaseKernel H D E
        (fun d e ↦ lambdaD d * lambdaE e) =
      BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum
          H D lambdaD *
        BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum
          H E lambdaE := by
  classical
  unfold doubledSelbergTensorBaseKernel
    BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum
    WithinFamilyCrossCoordinateCoprime
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  by_cases hD : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d'
  <;> by_cases hE : BoundedGaps.Maynard.IsCrossCoordinateCoprime H e e'
  <;> simp [hD, hE, firstLcmProduct, companionLcmProduct,
    BoundedGaps.Maynard.divisorTupleLcm]
  <;> ring

/-- Tensor-coefficient form of the complete normalization-kernel
decomposition.  The leading term is exactly the product of the two ordinary
compatible Maynard quadratics; the two displayed correction terms are the
precise analytic remainder that must be controlled uniformly in `m` and
`q`. -/
theorem doubledSelbergCrossTotientKernel_tensor_eq_quadratics_add_corrections_standard
    (H : Finset ℕ) (RD RE W m q : ℕ)
    (a b : (H → ℕ) → ℝ)
    (hm : 0 < m) (hq : q.Prime) (hRDq : RD ≤ q) (hREq : RE ≤ q)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W) :
    doubledSelbergCrossTotientKernel H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
        (fun d e ↦ a d * b e) m q =
      BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W) a *
        BoundedGaps.Maynard.compatibleDivisorPairNormalizedMainSum H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m)) b +
        doubledSelbergCompatibleAmplificationCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          (fun d e ↦ a d * b e) m q -
        doubledSelbergIncompatibleRemovalCorrection H
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RD W)
          (BoundedGaps.Maynard.maynardDivisorTupleSupport H RE (W * m))
          (fun d e ↦ a d * b e) m q := by
  rw [doubledSelbergCrossTotientKernel_eq_tensorBase_add_corrections_standard
    H RD RE W m q (fun d e ↦ a d * b e) hm hq hRDq hREq hcover]
  rw [doubledSelbergTensorBaseKernel_tensor]

end

end Erdos4b
