import ErdosProblems.Erdos237b.DyadicWeights
import ErdosProblems.Erdos237b.BoxVariational
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Unbounded variational ratios in the finite box model

This combines the dyadic identities and first-moment truncation. The ratio
is greater than `L / 32` when `k ≥ 2^L`; taking larger `L` makes it unbounded.
This is an unconditional finite-sum theorem. Converting it to an assertion
about primes still requires the sieve asymptotics for these box weights.
-/

namespace Erdos237b

open Finset
open scoped BigOperators

noncomputable def dyadicSquareMass (L k : ℕ) (j : Fin L) : ℝ :=
  dyadicHeight L j ^ 2 * dyadicLength L k j

noncomputable def dyadicLinearMass (L k : ℕ) (j : Fin L) : ℝ :=
  dyadicHeight L j * dyadicLength L k j

theorem dyadicSquareMass_nonneg (L k : ℕ) (j : Fin L) :
    0 ≤ dyadicSquareMass L k j := by
  unfold dyadicSquareMass dyadicHeight dyadicLength
  positivity

theorem sum_dyadicSquareMass_pos {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    0 < ∑ j, dyadicSquareMass L k j := by
  unfold dyadicSquareMass
  rw [sum_dyadicHeight_sq_mul_length]
  have hZ : 0 < dyadicNormalizer L := zero_lt_one.trans_le (one_le_dyadicNormalizer hL)
  positivity

theorem dyadicSquareMass_normalized {L k : ℕ} (hL : 0 < L) (hk : 0 < k)
    (j : Fin L) :
    dyadicSquareMass L k j / (∑ a, dyadicSquareMass L k a) = dyadicProbability L j := by
  unfold dyadicSquareMass
  rw [sum_dyadicHeight_sq_mul_length, dyadicHeight_sq_mul_length]
  unfold dyadicProbability
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hZ : dyadicNormalizer L ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (one_le_dyadicNormalizer hL))
  field_simp

theorem dyadic_boxDenominator_pos {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    0 < boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k := by
  apply boxDenominator_pos _ _ (dyadicSquareMass_nonneg L k) k (⟨0, hL⟩ : Fin L)
  · unfold dyadicSquareMass dyadicHeight dyadicLength
    positivity
  · have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    unfold dyadicUpper
    norm_num
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * L * k)).2
    nlinarith

theorem dyadic_box_ratio_gt {L k : ℕ} (hL : 0 < L) (hk : 2 ^ L ≤ k) :
    (L : ℝ) / 32 <
      (k : ℝ) * boxFaceNumerator (dyadicSquareMass L k) (dyadicLinearMass L k)
        (dyadicUpper L k) (k - 1) /
          boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k := by
  have hkpos : 0 < k := (pow_pos (by decide : 0 < (2 : ℕ)) L).trans_le hk
  have hmean : ((k - 1 : ℕ) : ℝ) *
      (∑ a, dyadicUpper L k a *
        (dyadicSquareMass L k a / ∑ b, dyadicSquareMass L k b)) ≤ 1 / 4 := by
    simp_rw [dyadicSquareMass_normalized hL hkpos]
    exact dyadic_mean_le_quarter hL hkpos (Nat.sub_le k 1)
  have hratio := box_ratio_lower_bound (dyadicSquareMass L k) (dyadicLinearMass L k)
    (dyadicUpper L k) (dyadicSquareMass_nonneg L k) (dyadicUpper_nonneg L k)
    (dyadicUpper_le_half hL hk) (k - 1) (sum_dyadicSquareMass_pos hL hkpos) hmean
    (by simpa only [Nat.sub_add_cancel hkpos] using dyadic_boxDenominator_pos hL hkpos)
  rw [Nat.sub_add_cancel hkpos] at hratio
  exact (dyadic_scalar_ratio_lower_bound hL hkpos).trans_le hratio

/-- For every real threshold, some finite box model has a larger ratio.
The dimension is chosen symbolically; no large finite set is evaluated. -/
theorem exists_dyadic_box_ratio_gt (C : ℝ) :
    ∃ L k : ℕ, 0 < L ∧ 0 < k ∧
      C < (k : ℝ) * boxFaceNumerator (dyadicSquareMass L k) (dyadicLinearMass L k)
        (dyadicUpper L k) (k - 1) /
          boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (32 * C) 0)
  have hLpos : 0 < L := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hL)
  refine ⟨L, 2 ^ L, hLpos, pow_pos (by decide) _, ?_⟩
  have hCL : C < (L : ℝ) / 32 := by linarith [le_max_left (32 * C) 0]
  exact hCL.trans (dyadic_box_ratio_gt hLpos le_rfl)

end Erdos237b
