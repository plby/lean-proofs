/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminarySurvivalScalar

/-!
# Scalar estimate for the sharp Bonferroni survival bound

For prescriptions of bounded size, the pairwise-overlap correction is
absorbed by lowering the pair-star supply from `d` to `d - K`.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

lemma choose_two_le_mul_of_le (k K : ℕ) (hk : k ≤ K) :
    k.choose 2 ≤ k * K := by
  rw [Nat.choose_two_right]
  calc
    k * (k - 1) / 2 ≤ k * (k - 1) := Nat.div_le_self _ _
    _ ≤ k * K := Nat.mul_le_mul_left k (by omega)

lemma mul_sub_choose_ge_mul_sub_cutoff
    (k d K : ℕ) (hk : k ≤ K) :
    k * (d - K) ≤ k * d - k.choose 2 := by
  rw [Nat.mul_sub_left_distrib]
  exact Nat.sub_le_sub_left
    (choose_two_le_mul_of_le k K hk) (k * d)

/-- Uniform exponential bound for the sharp one-step survival numerator.
The total number `k` of protected edges may vary, but is at most `K`. -/
theorem sharp_survival_scalar_of_card_le
    (A M d K k : ℕ)
    (hA : 0 < A) (hAM : A ≤ M) (hdM : d ≤ M)
    (hk : k ≤ K) :
    ((A - (k * d - k.choose 2) : ℕ) : ℝ≥0) *
        (A : ℝ≥0)⁻¹ ≤
      (((M - (d - K) : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^ k := by
  have heffM : d - K ≤ M := (Nat.sub_le d K).trans hdM
  have hloss : k * (d - K) ≤ k * d - k.choose 2 :=
    mul_sub_choose_ge_mul_sub_cutoff k d K hk
  have hsub : A - (k * d - k.choose 2) ≤ A - k * (d - K) := by
    omega
  calc
    ((A - (k * d - k.choose 2) : ℕ) : ℝ≥0) *
        (A : ℝ≥0)⁻¹ ≤
      ((A - k * (d - K) : ℕ) : ℝ≥0) * (A : ℝ≥0)⁻¹ := by
        gcongr
    _ ≤ (((M - (d - K) : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^ k :=
      nat_sub_mul_inv_le_sub_ratio_pow A M (d - K) k hA hAM heffM

/-- The common survival factor used for all bounded prescriptions. -/
def boundedSharpSurvivalTheta (M d K : ℕ) : ℝ≥0 :=
  ((M - (d - K) : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹

/-- A point-selection envelope which pays the largest possible survival
exponent in advance. -/
def boundedSharpTransferRho (D M d K : ℕ) : ℝ≥0 :=
  (D : ℝ≥0)⁻¹ * (boundedSharpSurvivalTheta M d K ^ K)⁻¹

lemma boundedSharpSurvivalTheta_le_one
    (M d K : ℕ) (hM : 0 < M) :
    boundedSharpSurvivalTheta M d K ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  simp only [boundedSharpSurvivalTheta, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_inv, NNReal.coe_one]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [← div_eq_mul_inv, div_le_one hMr]
  exact_mod_cast Nat.sub_le M (d - K)

lemma boundedSharpSurvivalTheta_pos
    (M d K : ℕ) (heff : d - K < M) :
    0 < boundedSharpSurvivalTheta M d K := by
  rw [← NNReal.coe_pos]
  simp only [boundedSharpSurvivalTheta, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_inv]
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) heff
  have hnum : 0 < M - (d - K) := Nat.sub_pos_of_lt heff
  positivity

/-- The worst-exponent point envelope dominates every smaller exponent. -/
lemma inv_le_pow_mul_boundedSharpTransferRho
    (D M d K k : ℕ) (hk : k ≤ K)
    (hM : 0 < M)
    (hpos : 0 < boundedSharpSurvivalTheta M d K) :
    (D : ℝ≥0)⁻¹ ≤
      boundedSharpSurvivalTheta M d K ^ k *
        boundedSharpTransferRho D M d K := by
  let theta := boundedSharpSurvivalTheta M d K
  have hthetaOne : theta ^ K * (theta ^ K)⁻¹ = 1 := by
    exact mul_inv_cancel₀ (pow_ne_zero K (ne_of_gt hpos))
  have hpow : theta ^ K ≤ theta ^ k := by
    exact pow_le_pow_right_of_le_one'
      (boundedSharpSurvivalTheta_le_one M d K hM) hk
  calc
    (D : ℝ≥0)⁻¹ = (D : ℝ≥0)⁻¹ * 1 := by simp
    _ = (D : ℝ≥0)⁻¹ * (theta ^ K * (theta ^ K)⁻¹) := by rw [hthetaOne]
    _ ≤ (D : ℝ≥0)⁻¹ * (theta ^ k * (theta ^ K)⁻¹) := by
      gcongr
    _ = theta ^ k * boundedSharpTransferRho D M d K := by
      simp only [boundedSharpTransferRho, theta]
      ring

end

end Erdos207
