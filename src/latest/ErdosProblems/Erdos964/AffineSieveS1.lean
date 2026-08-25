import ErdosProblems.Erdos964.AffineSieveSupport
import BoundedGaps.Maynard.ImprovedGPY.MainTerm

/-!
# The first sieve sum for affine forms

The exact finite main term is the same compatible divisor-pair sum as for
shifts. The only arithmetic error is the at-most-one CRT counting error
for each pair; no asymptotic hypothesis is used here.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable def affineSquareSieveWeight {H : Finset ℕ} (A B : H → ℕ)
    (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ) (v W n : ℕ) : ℝ := by
  classical
  exact if n ≡ v [MOD W] then
    (∑ d ∈ D.filter (affineDivisorTupleCondition A B n), lambda d) ^ 2 else 0

theorem affineSquareSieveWeight_nonneg {H : Finset ℕ} (A B : H → ℕ)
    (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ) (v W n : ℕ) :
    0 ≤ affineSquareSieveWeight A B D lambda v W n := by
  classical
  unfold affineSquareSieveWeight
  split_ifs <;> positivity

open scoped Classical in
theorem affineSquareSieveWeight_eq_pair_indicator {H : Finset ℕ} (A B : H → ℕ)
    (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ) (v W n : ℕ) :
    affineSquareSieveWeight A B D lambda v W n =
      ∑ d ∈ D, ∑ e ∈ D,
        if n ≡ v [MOD W] ∧ affineDivisorPairCondition A B n d e
        then lambda d * lambda e else 0 := by
  classical
  by_cases hn : n ≡ v [MOD W]
  · simp only [affineSquareSieveWeight, if_pos hn, pow_two,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : affineDivisorTupleCondition A B n d
    · simp only [if_pos hd]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : affineDivisorTupleCondition A B n e <;>
        simp [affineDivisorPairCondition, hn, hd, he, mul_comm]
    · simp [affineDivisorPairCondition, hn, hd]
  · simp [affineSquareSieveWeight, hn]

noncomputable def affineDivisorPairCount {H : Finset ℕ} (A B : H → ℕ)
    (v W N : ℕ) (d e : H → ℕ) : ℕ := by
  classical
  exact ((Finset.Ico N (2 * N)).filter (fun n =>
    n ≡ v [MOD W] ∧ affineDivisorPairCondition A B n d e)).card

theorem affineSieveWeightSum_eq_pair_card_sum {H : Finset ℕ} (A B : H → ℕ)
    (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ) (v W N : ℕ) :
    (∑ n ∈ Finset.Ico N (2 * N), affineSquareSieveWeight A B D lambda v W n) =
      ∑ d ∈ D, ∑ e ∈ D,
        (affineDivisorPairCount A B v W N d e : ℝ) * (lambda d * lambda e) := by
  classical
  simp_rw [affineSquareSieveWeight_eq_pair_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [affineDivisorPairCount, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]

theorem affineDivisorPairCount_eq_zero_of_not_cross
    {H : Finset ℕ} (A B : H → ℕ) {R W : ℕ} (v N : ℕ) (d e : H → ℕ)
    (hd : IsMaynardDivisorTuple H R W d) (he : IsMaynardDivisorTuple H R W e)
    (hcover : CoversAffineDeterminantPrimes A B W)
    (hcross : ¬ IsCrossCoordinateCoprime H d e) :
    affineDivisorPairCount A B v W N d e = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  exact hcross (affine_pair_implies_cross_coprime hd he hcover (Finset.mem_filter.mp hn).2.2)

open scoped Classical in
theorem affineSieveWeightSum_eq_compatible_pair_card_sum
    {H : Finset ℕ} (A B : H → ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    {R W : ℕ} (v N : ℕ) (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcover : CoversAffineDeterminantPrimes A B W) :
    (∑ n ∈ Finset.Ico N (2 * N), affineSquareSieveWeight A B D lambda v W n) =
      ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
        (affineDivisorPairCount A B v W N d e : ℝ) * (lambda d * lambda e) := by
  classical
  rw [affineSieveWeightSum_eq_pair_card_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hcross : IsCrossCoordinateCoprime H d e
  · rw [if_pos (c := IsCrossCoordinateCoprime H d e) hcross]
  · rw [if_neg hcross, affineDivisorPairCount_eq_zero_of_not_cross A B v N d e
      (hD d hd) (hD e he) hcover hcross, Nat.cast_zero, zero_mul]

theorem affineSieveWeightSum_sub_main_le_coefficientMass
    {H : Finset ℕ} (A B : H → ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    {R W : ℕ} (v N : ℕ) (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hlead : CoversAffineLeadingPrimes A W)
    (hdet : CoversAffineDeterminantPrimes A B W) :
    |(∑ n ∈ Finset.Ico N (2 * N), affineSquareSieveWeight A B D lambda v W n) -
        (N : ℝ) / W * compatibleDivisorPairNormalizedMainSum H D lambda| ≤
      compatibleDivisorPairCoefficientMass H D lambda := by
  classical
  rw [affineSieveWeightSum_eq_compatible_pair_card_sum A B D lambda v N hD hdet,
    ← compatibleDivisorPairMainSum_eq_factor_normalized]
  unfold compatibleDivisorPairMainSum compatibleDivisorPairCoefficientMass
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨heD, hcross⟩ := Finset.mem_filter.mp he
  rw [abs_mul]
  have herr := affine_divisor_pair_count_error_le_one A B v N d e hW
    (hD d hd) (hD e heD) hcross hlead
  exact (mul_le_mul_of_nonneg_right herr (abs_nonneg _)).trans_eq (one_mul _)

end Erdos964
