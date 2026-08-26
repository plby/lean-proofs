/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SingularSeriesAverage

/-!
# A weighted first-order lower bound for the inverse singular factor

Nonnegative weights allow Bonferroni's inequality to be summed before
estimating the collision losses. Only one additional prime congruence
occurs in each loss term. Primes dividing the cofactor remain in their
exact fixed multiplicative factor.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def weightedAffineCollisionSum {H : Finset ℕ} (A B m p : ℕ)
    (ba : H × H) (W : ℕ → ℝ) : ℝ :=
  ∑ q ∈ affineCollisionAuxiliaryPrimes A B m p ba, W q

def weightedSingularCollisionLoss (K w y m A B : ℕ) (W : ℕ → ℝ) : ℝ :=
  ∑ p ∈ varyingSingularPrimeSupport w y m,
    ((4 * K : ℕ) : ℝ) / p *
      ∑ ba ∈ BoundedGaps.Maynard.offDiagonalPairs (preSievedShifts K w),
        weightedAffineCollisionSum A B m p ba W

theorem sum_weighted_localPenalty_le_affineCollisionSum
    {K w A B m p : ℕ} (hfour : 4 * K ≤ w) (hp : p.Prime)
    (hwp : w < p) (hpm : ¬p ∣ m) (hpA : p < A)
    (W : ℕ → ℝ) (hW : ∀ q ∈ auxiliaryPrimeInterval A B, 0 ≤ W q) :
    (∑ q ∈ auxiliaryPrimeInterval A B,
      W q * largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
      ((4 * K : ℕ) : ℝ) / p *
        ∑ ba ∈ BoundedGaps.Maynard.offDiagonalPairs (preSievedShifts K w),
          weightedAffineCollisionSum A B m p ba W := by
  classical
  have hpq : ∀ q ∈ auxiliaryPrimeInterval A B, ¬p ∣ q := by
    intro q hq hd
    have hqd := mem_auxiliaryPrimeInterval.mp hq
    rcases (Nat.dvd_prime hqd.2.2).mp hd with h1 | heq
    · exact hp.ne_one h1
    · omega
  calc
    _ ≤ ∑ q ∈ auxiliaryPrimeInterval A B,
        W q * ∑ ba ∈ BoundedGaps.Maynard.offDiagonalPairs (preSievedShifts K w),
          if (p : ℤ) ∣ crossAffineDifference m q ba then ((4 * K : ℕ) : ℝ) / p else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (largeGapLocalPenalty_le_offDiagonal_affine_sum hfour hp hwp hpm (hpq q hq)) (hW q hq)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ba hba
      unfold weightedAffineCollisionSum affineCollisionAuxiliaryPrimes
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> ring

theorem weighted_varyingSingularInverseProduct_lower
    {K w y m A B : ℕ} (hfour : 4 * K ≤ w) (hyA : y < A)
    (W : ℕ → ℝ) (hW : ∀ q ∈ auxiliaryPrimeInterval A B, 0 ≤ W q) :
    (∑ q ∈ auxiliaryPrimeInterval A B, W q) - weightedSingularCollisionLoss K w y m A B W ≤
      ∑ q ∈ auxiliaryPrimeInterval A B, W q * varyingSingularInverseProduct K w y m q := by
  have hlarge : ∀ p ∈ varyingSingularPrimeSupport w y m,
      2 * (preSievedShifts K w).card < p := by
    intro p hp
    have hd := mem_varyingSingularPrimeSupport.mp hp
    rw [card_preSievedShifts]
    omega
  have hbon : ∀ q ∈ auxiliaryPrimeInterval A B,
      W q * (1 - ∑ p ∈ varyingSingularPrimeSupport w y m,
        largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
          W q * varyingSingularInverseProduct K w y m q := by
    intro q hq
    exact mul_le_mul_of_nonneg_left
      (one_sub_sum_largeGapLocalPenalty_le_prod_amplification_inv _ hlarge) (hW q hq)
  have hloss : (∑ p ∈ varyingSingularPrimeSupport w y m,
      ∑ q ∈ auxiliaryPrimeInterval A B,
        W q * largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
      weightedSingularCollisionLoss K w y m A B W := by
    apply Finset.sum_le_sum
    intro p hp
    have hd := mem_varyingSingularPrimeSupport.mp hp
    exact sum_weighted_localPenalty_le_affineCollisionSum hfour hd.2.2.1 hd.1 hd.2.2.2
      (hd.2.1.trans_lt hyA) W hW
  calc
    _ ≤ (∑ q ∈ auxiliaryPrimeInterval A B, W q) -
        ∑ p ∈ varyingSingularPrimeSupport w y m,
          ∑ q ∈ auxiliaryPrimeInterval A B,
            W q * largeGapLocalPenalty (preSievedShifts K w) m q p :=
      sub_le_sub_left hloss _
    _ = ∑ q ∈ auxiliaryPrimeInterval A B,
        W q * (1 - ∑ p ∈ varyingSingularPrimeSupport w y m,
          largeGapLocalPenalty (preSievedShifts K w) m q p) := by
      simp_rw [mul_sub, mul_one, Finset.mul_sum]
      rw [Finset.sum_sub_distrib, Finset.sum_comm]
    _ ≤ _ := Finset.sum_le_sum hbon

theorem weighted_roughSingularInverseProduct_lower
    {K w y m A B : ℕ} (hfour : 4 * K ≤ w) (hw : 0 < w) (hyA : y < A)
    (W : ℕ → ℝ) (hW : ∀ q ∈ auxiliaryPrimeInterval A B, 0 ≤ W q) :
    fixedSingularInverseFactor K w y m *
      ((∑ q ∈ auxiliaryPrimeInterval A B, W q) - weightedSingularCollisionLoss K w y m A B W) ≤
        ∑ q ∈ auxiliaryPrimeInterval A B, W q * roughSingularInverseProduct K w y m q := by
  have he := mul_le_mul_of_nonneg_left
    (weighted_varyingSingularInverseProduct_lower (m := m) hfour hyA W hW)
    (fixedSingularInverseFactor_pos (y := y) (m := m) hfour hw).le
  refine he.trans_eq ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [roughSingularInverseProduct_eq_fixed_mul_varying hfour hyA hq]
  ring

theorem weighted_universal_div_largeGapSingularSeries_lower
    {K w y m A B : ℕ} (hfour : 4 * K ≤ w) (hw : 0 < w)
    (hwy : w ≤ y) (hyA : y < A) (hm : Even m)
    (W : ℕ → ℝ) (hW : ∀ q ∈ auxiliaryPrimeInterval A B, 0 ≤ W q) :
    fixedSingularInverseFactor K w y m *
      ((∑ q ∈ auxiliaryPrimeInterval A B, W q) - weightedSingularCollisionLoss K w y m A B W) ≤
        ∑ q ∈ auxiliaryPrimeInterval A B, W q *
          ((largeGapSingularSeries (preSievedShifts K w) m q w *
            genericRoughSingularProduct K w y) /
            largeGapSingularSeries (preSievedShifts K w) m q y) := by
  have h := weighted_roughSingularInverseProduct_lower (m := m) hfour hw hyA W hW
  simpa only [roughSingularInverseProduct_eq_universal_div_singularSeries hfour hwy hm] using h

end

end Erdos4b
