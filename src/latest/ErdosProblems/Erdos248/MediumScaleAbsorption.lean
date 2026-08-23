import ErdosProblems.Erdos248.MediumSumBounds
import ErdosProblems.Erdos248.MomentScaleBounds

/-!
# Erdős Problem 248: absorbing the medium-prime scale errors

The medium event estimates leave reciprocal-prime sums, inverse-cutoff
remainders, and a rough cross-tail.  This file combines the elementary sums
with the scale inequalities to replace all such terms by fixed constants.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

/-- The whole medium range is contained in the far range at the endpoint
`k = K`; hence its ordinary reciprocal mass is `O(K)`. -/
theorem sum_mediumPrimes_inv_le_farPrimeReciprocalConstant_mul
    {K : ℕ} (m : nearShifts K) :
    (∑ p ∈ mediumPrimes K m, (1 : ℝ) / (p : ℝ)) ≤
      farPrimeReciprocalConstant * (K : ℝ) := by
  have hK : 0 < K := lt_of_lt_of_le
    (mem_nearShifts.mp m.2).1 (mem_nearShifts.mp m.2).2
  have hmax : max (tinyCutoff K) K = tinyCutoff K :=
    max_eq_left (K_le_tinyCutoff K)
  have hradius : shiftRadius K m ≤ shiftRadius K 1 := by
    unfold shiftRadius
    apply Nat.pow_le_pow_right (by norm_num)
    apply Nat.pow_le_pow_right (by norm_num)
    exact Nat.sub_le_sub_left (mem_nearShifts.mp m.2).1 (100 * K)
  have hsubset : mediumPrimes K m ⊆ farPrimes K K := by
    intro p hp
    unfold mediumPrimes at hp
    unfold farPrimes
    rw [mem_primesBetween] at hp ⊢
    rw [hmax]
    exact ⟨hp.1, hp.2.1.trans hradius, hp.2.2⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun p hp hpnot => by positivity)).trans
      (sum_farPrimes_inv_le hK le_rfl)

/-- Two powers of `K`, even with the correlation factor `96^K`, are
absorbed by `tinyCutoff K + 1`. -/
theorem real_second_ninetySix_div_tiny_add_one_le_one
    {K : ℕ} (hK : 0 < K) :
    (K : ℝ) ^ 2 * 96 ^ K /
        ((tinyCutoff K + 1 : ℕ) : ℝ) ≤ 1 := by
  have hpow : K ^ 2 ≤ K ^ 5 :=
    Nat.pow_le_pow_right hK (by norm_num)
  have hnat : K ^ 2 * 96 ^ K ≤ tinyCutoff K :=
    (Nat.mul_le_mul_right (96 ^ K) hpow).trans
      (fifth_mul_ninetySixPow_le_tinyCutoff hK)
  have hden : (0 : ℝ) < ((tinyCutoff K + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  norm_num
  exact_mod_cast hnat.trans (Nat.le_succ (tinyCutoff K))

theorem real_second_div_tiny_add_one_le_one
    {K : ℕ} (hK : 0 < K) :
    (K : ℝ) ^ 2 / ((tinyCutoff K + 1 : ℕ) : ℝ) ≤ 1 := by
  have h96pos : 0 < 96 ^ K := pow_pos (by norm_num) K
  have hnat0 : K ^ 2 ≤ K ^ 2 * 96 ^ K :=
    Nat.le_mul_of_pos_right _ h96pos
  have hpow : K ^ 2 ≤ K ^ 5 :=
    Nat.pow_le_pow_right hK (by norm_num)
  have hnat : K ^ 2 ≤ tinyCutoff K :=
    hnat0.trans ((Nat.mul_le_mul_right (96 ^ K) hpow).trans
      (fifth_mul_ninetySixPow_le_tinyCutoff hK))
  have hden : (0 : ℝ) < ((tinyCutoff K + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  norm_num
  exact_mod_cast hnat.trans (Nat.le_succ (tinyCutoff K))

/-- The residual part of the bundled one-prime cost remains bounded after
the correlation factor is inserted. -/
theorem ninetySixPow_mul_singleResidual_le_sixteen
    {K : ℕ} (hK : 0 < K) :
    96 ^ K *
        (16 * (K : ℝ) ^ 2 /
          ((tinyCutoff K + 1 : ℕ) : ℝ)) ≤ 16 := by
  calc
    96 ^ K *
          (16 * (K : ℝ) ^ 2 /
            ((tinyCutoff K + 1 : ℕ) : ℝ)) =
        16 * ((K : ℝ) ^ 2 * 96 ^ K /
          ((tinyCutoff K + 1 : ℕ) : ℝ)) := by ring
    _ ≤ 16 * 1 := by
      gcongr
      exact real_second_ninetySix_div_tiny_add_one_le_one hK
    _ = 16 := by ring

/-- The leading bilinear displacement contribution is already a fixed
multiple of the normalized logarithmic constant. -/
theorem sixtyFour_mul_sq_sum_mediumDisplacement_le
    {K : ℕ} (m : nearShifts K) :
    64 *
        (∑ p ∈ mediumPrimes K m,
          primeLogDisplacement K m p / (p : ℝ)) ^ 2 ≤
      64 * normalizedPrimeLogSquareConstant ^ 2 := by
  exact mul_le_mul_of_nonneg_left
    (sq_sum_mediumPrimes_primeLogDisplacement_div_le m) (by norm_num)

/-- The first pair cross-remainder, including its `K²` and `96^K`
coefficients, is absolutely bounded. -/
theorem ninetySixPow_mul_mediumPairFirstCross_le
    {K : ℕ} (hK : 0 < K) (m : nearShifts K) :
    16 * (K : ℝ) ^ 2 * 96 ^ K *
        ((∑ p ∈ mediumPrimes K m,
            (1 : ℝ) /
              ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) *
          (∑ p ∈ mediumPrimes K m,
            primeLogDisplacement K m p ^ 2 / (p : ℝ))) ≤
      128 * normalizedPrimeLogSquareConstant := by
  calc
    16 * (K : ℝ) ^ 2 * 96 ^ K *
          ((∑ p ∈ mediumPrimes K m,
              (1 : ℝ) /
                ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) *
            (∑ p ∈ mediumPrimes K m,
              primeLogDisplacement K m p ^ 2 / (p : ℝ))) ≤
        16 * (K : ℝ) ^ 2 * 96 ^ K *
          ((8 / ((tinyCutoff K + 1 : ℕ) : ℝ)) *
            normalizedPrimeLogSquareConstant) := by
      exact mul_le_mul_of_nonneg_left
        (mul_sum_mediumPredSq_sum_displacementSq_le m) (by positivity)
    _ = 128 *
        ((K : ℝ) ^ 2 * 96 ^ K /
          ((tinyCutoff K + 1 : ℕ) : ℝ)) *
        normalizedPrimeLogSquareConstant := by ring
    _ ≤ 128 * 1 * normalizedPrimeLogSquareConstant := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (real_second_ninetySix_div_tiny_add_one_le_one hK) (by norm_num))
        normalizedPrimeLogSquareConstant_nonneg
    _ = 128 * normalizedPrimeLogSquareConstant := by ring

/-- The second pair cross-remainder, including its `K²` and `96^K`
coefficients, is bounded by an affine expression in the normalized
logarithmic constant. -/
theorem ninetySixPow_mul_mediumPairSecondCross_le
    {K : ℕ} (hK : 0 < K) (m : nearShifts K) :
    2 * (K : ℝ) ^ 2 * 96 ^ K *
        ((∑ p ∈ mediumPrimes K m,
            (1 : ℝ) /
              ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) *
          (∑ p ∈ mediumPrimes K m,
            (2 * primeLogDisplacement K m p +
              (K : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 2 / (p : ℝ))) ≤
      128 * normalizedPrimeLogSquareConstant + 256 := by
  let x : ℝ := (K : ℝ) ^ 2 * 96 ^ K /
    ((tinyCutoff K + 1 : ℕ) : ℝ)
  let y : ℝ := (K : ℝ) ^ 2 /
    ((tinyCutoff K + 1 : ℕ) : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hx1 : x ≤ 1 := by
    simpa [x] using real_second_ninetySix_div_tiny_add_one_le_one hK
  have hy1 : y ≤ 1 := by
    simpa [y] using real_second_div_tiny_add_one_le_one hK
  calc
    2 * (K : ℝ) ^ 2 * 96 ^ K *
          ((∑ p ∈ mediumPrimes K m,
              (1 : ℝ) /
                ((p : ℝ) * (((p - 1 : ℕ) : ℝ) ^ 2))) *
            (∑ p ∈ mediumPrimes K m,
              (2 * primeLogDisplacement K m p +
                (K : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 2 / (p : ℝ))) ≤
        2 * (K : ℝ) ^ 2 * 96 ^ K *
          ((8 / ((tinyCutoff K + 1 : ℕ) : ℝ)) *
            (8 * normalizedPrimeLogSquareConstant +
              16 * (K : ℝ) ^ 2 /
                ((tinyCutoff K + 1 : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_sum_mediumPredSq_sum_singleDisplacementCost_le m) (by positivity)
    _ = 16 * x *
        (8 * normalizedPrimeLogSquareConstant + 16 * y) := by
      dsimp [x, y]
      ring
    _ ≤ 16 * 1 *
        (8 * normalizedPrimeLogSquareConstant + 16 * y) := by
      have hbracket : 0 ≤
          8 * normalizedPrimeLogSquareConstant + 16 * y :=
        add_nonneg
          (mul_nonneg (by norm_num) normalizedPrimeLogSquareConstant_nonneg)
          (mul_nonneg (by norm_num) hy0)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx1 (by norm_num)) hbracket
    _ ≤ 16 * 1 *
        (8 * normalizedPrimeLogSquareConstant + 16 * 1) := by
      have hyterm : 16 * y ≤ 16 * 1 :=
        mul_le_mul_of_nonneg_left hy1 (by norm_num)
      have hadd :
          8 * normalizedPrimeLogSquareConstant + 16 * y ≤
            8 * normalizedPrimeLogSquareConstant + 16 * 1 :=
        add_le_add_right hyterm _
      exact mul_le_mul_of_nonneg_left
        hadd (by norm_num)
    _ = 128 * normalizedPrimeLogSquareConstant + 256 := by ring

/-- The rough cross-tail times the square of the unweighted medium-prime
reciprocal mass is absolutely bounded. -/
theorem crossTail_mul_ninetySixPow_mul_sum_mediumInv_le
    {K : ℕ} (hK : 0 < K) (m : nearShifts K) :
    roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
        (globalRadius K) * 96 ^ K *
      (∑ p ∈ mediumPrimes K m, (1 : ℝ) / (p : ℝ)) ≤
      196608 * farPrimeReciprocalConstant := by
  let T : ℝ := roughCrossTupleTotientSquareTail (nearShifts K)
    (tinyCutoff K) (globalRadius K)
  let S : ℝ := ∑ p ∈ mediumPrimes K m, (1 : ℝ) / (p : ℝ)
  let C : ℝ := farPrimeReciprocalConstant
  have hT0 : 0 ≤ T := by
    dsimp [T]
    unfold roughCrossTupleTotientSquareTail
    exact Finset.sum_nonneg fun s hs ↦ by
      unfold crossTotientSquareWeight
      positivity
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun p hp ↦ by positivity
  have hC0 : 0 ≤ C := farPrimeReciprocalConstant_nonneg
  have hS : S ≤ C * (K : ℝ) := by
    simpa [S, C] using
      sum_mediumPrimes_inv_le_farPrimeReciprocalConstant_mul m
  have hKleFourth : (K : ℝ) ≤ (K : ℝ) ^ 4 := by
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [sq_nonneg ((K : ℝ) ^ 2 - 1),
      sq_nonneg ((K : ℝ) - 1)]
  have hcross : T * 96 ^ K * (K : ℝ) ^ 4 ≤ 196608 := by
    simpa [T] using crossTail_mul_ninetySixPow_mul_fourth_le hK
  calc
    T * 96 ^ K * S ≤ T * 96 ^ K * (C * (K : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hS
        (mul_nonneg hT0 (by positivity))
    _ = C * (T * 96 ^ K * (K : ℝ)) := by ring
    _ ≤ C * (T * 96 ^ K * (K : ℝ) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hKleFourth
          (mul_nonneg hT0 (by positivity))) hC0
    _ ≤ C * 196608 := mul_le_mul_of_nonneg_left hcross hC0
    _ = 196608 * C := by ring

theorem crossTail_mul_ninetySixPow_mul_sq_sum_mediumInv_le
    {K : ℕ} (hK : 0 < K) (m : nearShifts K) :
    roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
        (globalRadius K) * 96 ^ K *
      (∑ p ∈ mediumPrimes K m, (1 : ℝ) / (p : ℝ)) ^ 2 ≤
      196608 * farPrimeReciprocalConstant ^ 2 := by
  let T : ℝ := roughCrossTupleTotientSquareTail (nearShifts K)
    (tinyCutoff K) (globalRadius K)
  let S : ℝ := ∑ p ∈ mediumPrimes K m, (1 : ℝ) / (p : ℝ)
  let C : ℝ := farPrimeReciprocalConstant
  have hT0 : 0 ≤ T := by
    dsimp [T]
    unfold roughCrossTupleTotientSquareTail
    apply Finset.sum_nonneg
    intro s hs
    unfold crossTotientSquareWeight
    positivity
  have hS0 : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro p hp
    positivity
  have hC0 : 0 ≤ C := by
    exact farPrimeReciprocalConstant_nonneg
  have hS : S ≤ C * (K : ℝ) := by
    simpa [S, C] using
      sum_mediumPrimes_inv_le_farPrimeReciprocalConstant_mul m
  have hSsq : S ^ 2 ≤ (C * (K : ℝ)) ^ 2 :=
    (sq_le_sq₀ hS0 (mul_nonneg hC0 (by positivity))).mpr hS
  have hKsq_le_fourth : (K : ℝ) ^ 2 ≤ (K : ℝ) ^ 4 := by
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hKsqOne : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    calc
      (K : ℝ) ^ 2 = (K : ℝ) ^ 2 * 1 := by ring
      _ ≤ (K : ℝ) ^ 2 * (K : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hKsqOne (sq_nonneg _)
      _ = (K : ℝ) ^ 4 := by ring
  have hcross : T * 96 ^ K * (K : ℝ) ^ 4 ≤ 196608 := by
    simpa [T] using crossTail_mul_ninetySixPow_mul_fourth_le hK
  calc
    T * 96 ^ K * S ^ 2 ≤
        T * 96 ^ K * (C * (K : ℝ)) ^ 2 := by
      gcongr
    _ = C ^ 2 * (T * 96 ^ K * (K : ℝ) ^ 2) := by ring
    _ ≤ C ^ 2 * (T * 96 ^ K * (K : ℝ) ^ 4) := by
      gcongr
    _ ≤ C ^ 2 * 196608 := by
      gcongr
    _ = 196608 * C ^ 2 := by ring

end Erdos248
