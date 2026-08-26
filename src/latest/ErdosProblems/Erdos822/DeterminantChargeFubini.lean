/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SharpDeterminantPrimeAverage
import ErdosProblems.Erdos822.FixedCommonDivisorFiber

/-! # Exact finite rearrangements for the admissible determinant charge -/

namespace Erdos822

open scoped BigOperators Classical

noncomputable def fixedCommonDivisorLargePrimes
    (B : Finset ℕ) (N x k r m' h : ℕ) : Finset ℕ :=
  (largePrimes N).filter fun q ↦ k * r * q ∈ B ∧
    (outerCollisionPairs x (k * r * q) m').Nonempty ∧ h ∣ shiftedCoefficientGcd (k * r * q) m'

noncomputable def smallDeterminantMass (U z k r q m' h : ℕ) : ℝ :=
  ∑ p ∈ smallDeterminantPrimes U z k r h,
    if p ∣ reducedTotientDet (k * r * q) m' then (1 : ℝ) / p else 0

theorem smallDeterminantMass_nonneg (U z k r q m' h : ℕ) :
    0 ≤ smallDeterminantMass U z k r q m' h := by
  apply Finset.sum_nonneg
  intro p hp
  split_ifs <;> positivity

theorem smallDeterminantLargePrimeFiberIn_eq_fixed_filter
    (B : Finset ℕ) (N x k r m' p h : ℕ) :
    smallDeterminantLargePrimeFiberIn B N x k r m' p h =
      (fixedCommonDivisorLargePrimes B N x k r m' h).filter
        (fun q ↦ p ∣ reducedTotientDet (k * r * q) m') := by
  ext q
  simp only [mem_smallDeterminantLargePrimeFiberIn_iff,
    mem_smallDeterminantLargePrimeFiber_iff, fixedCommonDivisorLargePrimes, Finset.mem_filter]
  tauto

theorem sum_smallDeterminantMass_fixedLargePrimes_eq
    (B : Finset ℕ) (N x k r m' h U z : ℕ) :
    (∑ q ∈ fixedCommonDivisorLargePrimes B N x k r m' h,
      ((1 : ℝ) / q) * smallDeterminantMass U z k r q m' h) =
      ∑ p ∈ smallDeterminantPrimes U z k r h, ((1 : ℝ) / p) *
        ∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h, (1 : ℝ) / q := by
  unfold smallDeterminantMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smallDeterminantLargePrimeFiberIn_eq_fixed_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs <;> ring

theorem sum_smallDeterminantMass_fixedPairs_eq
    (B : Finset ℕ) (N x k m' h U z : ℕ) :
    (∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
      ((1 : ℝ) / (rq.1 * rq.2 : ℕ)) * smallDeterminantMass U z k rq.1 rq.2 m' h) =
      ∑ r ∈ middlePrimes N, ((1 : ℝ) / r) *
        ∑ q ∈ fixedCommonDivisorLargePrimes B N x k r m' h,
          ((1 : ℝ) / q) * smallDeterminantMass U z k r q m' h := by
  unfold fixedCommonDivisorPrimePairs fixedCommonDivisorLargePrimes
  rw [Finset.sum_filter]
  change (∑ rq ∈ middlePrimes N ×ˢ largePrimes N,
    if k * rq.1 * rq.2 ∈ B ∧ (outerCollisionPairs x (k * rq.1 * rq.2) m').Nonempty ∧
        h ∣ shiftedCoefficientGcd (k * rq.1 * rq.2) m' then
      ((1 : ℝ) / (rq.1 * rq.2 : ℕ)) * smallDeterminantMass U z k rq.1 rq.2 m' h else 0) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs <;> push_cast <;> ring

#print axioms sum_smallDeterminantMass_fixedPairs_eq

end Erdos822
