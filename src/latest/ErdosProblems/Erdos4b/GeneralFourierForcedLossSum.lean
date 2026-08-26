/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierRelativeProduct
import ErdosProblems.Erdos4b.SingularWeightedPrimeAverage

/-!
# Summing the reciprocal-prime main terms and the aggregate errors

The main contribution uses the reciprocal-square tail. The error uses
only `1 / p ≤ 1`, so no factor counting the forced primes is lost.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sum_reciprocal_main_error_le
    (P : Finset ℕ) {w : ℕ} (hw : 0 < w) (hrough : ∀ p ∈ P, w < p)
    {C : ℝ} (hC : 0 ≤ C) (E : ℕ → ℝ) (hE : ∀ p ∈ P, 0 ≤ E p) :
    (∑ p ∈ P, (C / p + E p) / p) ≤ 2 * C / w + ∑ p ∈ P, E p := by
  calc
    _ ≤ ∑ p ∈ P, (C * ((1 : ℝ) / (p : ℝ) ^ 2) + E p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by have := hrough p hp; omega : 1 ≤ p)
      calc
        _ = C * ((1 : ℝ) / (p : ℝ) ^ 2) + E p / p := by ring
        _ ≤ _ := add_le_add le_rfl (div_le_self (hE p hp) hp1)
    _ = C * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) + ∑ p ∈ P, E p := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ C * (2 / (w : ℝ)) + ∑ p ∈ P, E p :=
      add_le_add (mul_le_mul_of_nonneg_left
        (finite_rough_reciprocalSquare_sum_le P hw hrough) hC) le_rfl
    _ = _ := by ring

theorem card_preSieved_offDiagonalPairs_le (K w : ℕ) :
    (BoundedGaps.Maynard.offDiagonalPairs (preSievedShifts K w)).card ≤ K ^ 2 := by
  calc
    _ ≤ Fintype.card (↥(preSievedShifts K w) × ↥(preSievedShifts K w)) := Finset.card_le_univ _
    _ = _ := by rw [Fintype.card_prod, Fintype.card_coe, card_preSievedShifts, pow_two]

theorem weightedSingularCollisionLoss_nonneg
    (K w y m A B : ℕ) (W : ℕ → ℝ) (hW : ∀ q, 0 ≤ W q) :
    0 ≤ weightedSingularCollisionLoss K w y m A B W := by
  unfold weightedSingularCollisionLoss weightedAffineCollisionSum
  exact Finset.sum_nonneg fun p hp ↦ mul_nonneg (by positivity)
    (Finset.sum_nonneg fun ba hba ↦ Finset.sum_nonneg fun q hq ↦ hW q)

theorem normalized_weightedSingularCollisionLoss_le
    {K w y m A B : ℕ} (hw : 0 < w) (W : ℕ → ℝ)
    {ρ C : ℝ} (hC : 0 ≤ C) (E : ℕ → ℝ)
    (hE : ∀ p ∈ varyingSingularPrimeSupport w y m, 0 ≤ E p)
    (hbound : ∀ p ∈ varyingSingularPrimeSupport w y m,
      ∀ ba ∈ BoundedGaps.Maynard.offDiagonalPairs (preSievedShifts K w),
        ρ * weightedAffineCollisionSum A B m p ba W ≤ C / p + E p) :
    ρ * weightedSingularCollisionLoss K w y m A B W ≤
      (4 * K : ℝ) * (K : ℝ) ^ 2 *
        (2 * C / w + ∑ p ∈ varyingSingularPrimeSupport w y m, E p) := by
  let T := BoundedGaps.Maynard.offDiagonalPairs (preSievedShifts K w)
  have hrough : ∀ p ∈ varyingSingularPrimeSupport w y m, w < p :=
    fun p hp ↦ (mem_varyingSingularPrimeSupport.mp hp).1
  have hsum := sum_reciprocal_main_error_le (varyingSingularPrimeSupport w y m)
    hw hrough hC E hE
  have hcard : (T.card : ℝ) ≤ (K : ℝ) ^ 2 := by
    exact_mod_cast card_preSieved_offDiagonalPairs_le K w
  have hnonneg : 0 ≤ 2 * C / w + ∑ p ∈ varyingSingularPrimeSupport w y m, E p :=
    add_nonneg (by positivity) (Finset.sum_nonneg hE)
  calc
    _ = ∑ p ∈ varyingSingularPrimeSupport w y m,
        (4 * K : ℝ) / p * ∑ ba ∈ T, ρ * weightedAffineCollisionSum A B m p ba W := by
      unfold weightedSingularCollisionLoss
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      change ρ * ((4 * K : ℝ) / p * ∑ ba ∈ T, weightedAffineCollisionSum A B m p ba W) = _
      rw [← Finset.mul_sum]
      ring
    _ ≤ ∑ p ∈ varyingSingularPrimeSupport w y m,
        (4 * K : ℝ) / p * (T.card : ℝ) * (C / p + E p) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_le_sum (hbound p hp)).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul])
    _ = (4 * K : ℝ) * (T.card : ℝ) *
        ∑ p ∈ varyingSingularPrimeSupport w y m, (C / p + E p) / p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (4 * K : ℝ) * (T.card : ℝ) *
        (2 * C / w + ∑ p ∈ varyingSingularPrimeSupport w y m, E p) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by positivity)) hnonneg

end

end Erdos4b
