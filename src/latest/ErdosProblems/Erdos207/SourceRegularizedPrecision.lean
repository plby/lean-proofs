/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerExponentChoice
import ErdosProblems.Erdos207.PolynomialExponentialDecay

/-! # Explicit regularization precision supplies the sparse initial error and gap budgets -/

namespace Erdos207

theorem source_regularized_precision (t : ℝ) (b B : ℕ) (ht : 1 ≤ t) :
    0 < 1 / (24 * t ^ ksssPowerErrorExponent b B) ∧
      1 / (24 * t ^ ksssPowerErrorExponent b B) ≤ 1 / 2 ∧
      4 * (1 / (24 * t ^ ksssPowerErrorExponent b B)) =
        1 / (6 * t ^ ksssPowerErrorExponent b B) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hpow : 1 ≤ t ^ ksssPowerErrorExponent b B := one_le_pow₀ ht
  refine ⟨by positivity, ?_, by ring⟩
  apply (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 24)
    (by linarith : (24 : ℝ) ≤ 24 * t ^ ksssPowerErrorExponent b B)).trans
  norm_num

theorem source_regularized_gap_budget
    (q b B k Rmin d : ℕ) (n t x : ℝ) (ht : 49152 ≤ t) (hd : 1 ≤ d)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ n)
    (hratio : n / t ^ b ≤ x) :
    1 ≤ x ∧ 8192 * t ≤ 4 * (1 / (24 * t ^ ksssPowerErrorExponent b B)) * x ^ d := by
  let s := ksssPowerErrorExponent b B
  let R := ksssPowerDenominatorExponent q b B k Rmin
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hgap : s + b + 2 ≤ R := by
    dsimp only [s, R, ksssPowerDenominatorExponent, ksssPowerThetaExponent,
      ksssPowerJumpExponent, ksssPowerVarianceExponent, ksssPowerMarginExponent,
      ksssPowerErrorExponent, ksssPowerDeterministicExponent, ksssPowerRawVarianceExponent]
    omega
  have hn : t ^ (s + b + 2) ≤ n := (pow_le_pow_right₀ ht1 hgap).trans hscale
  have hx : 1 ≤ x := by
    apply le_trans _ hratio
    apply (le_div_iff₀ (pow_pos ht0 b)).mpr
    simpa only [one_mul] using (pow_le_pow_right₀ ht1 (show b ≤ s + b + 2 by omega)).trans hn
  have hbig : 49152 * t * t ^ (s + b) ≤ n := by
    calc
      _ ≤ t * t * t ^ (s + b) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ht ht0.le) (pow_nonneg ht0.le _)
      _ = t ^ (s + b + 2) := by rw [pow_add]; ring
      _ ≤ n := hn
  have hgapBase : 8192 * t ≤ n / (6 * t ^ (s + b)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      8192 * t * (6 * t ^ (s + b)) = 49152 * t * t ^ (s + b) := by ring
      _ ≤ n := hbig
  refine ⟨hx, hgapBase.trans ?_⟩
  calc
    _ = 4 * (1 / (24 * t ^ s)) * (n / t ^ b) := by rw [pow_add]; ring
    _ ≤ 4 * (1 / (24 * t ^ s)) * x := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ 4 * (1 / (24 * t ^ s)) * x ^ d := mul_le_mul_of_nonneg_left
      (by simpa only [pow_one] using pow_le_pow_right₀ hx hd) (by positivity)

theorem source_regularized_sampling_exponent
    (q b B k Rmin : ℕ) (n t p eta : ℝ) (ht : 1 ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ n)
    (hdensity : 24 / t ^ b ≤ p ^ 2 * eta) :
    t / 384 ≤ (1 / (24 * t ^ ksssPowerErrorExponent b B)) ^ 2 * (p ^ 2 * eta * n) / 16 := by
  let s := ksssPowerErrorExponent b B
  let R := ksssPowerDenominatorExponent q b B k Rmin
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hn0 : 0 ≤ n := (pow_nonneg ht0.le _).trans hscale
  have hgap : 2 * s + b + 1 ≤ R := by
    dsimp only [s, R, ksssPowerDenominatorExponent, ksssPowerThetaExponent,
      ksssPowerJumpExponent, ksssPowerVarianceExponent, ksssPowerMarginExponent,
      ksssPowerErrorExponent, ksssPowerDeterministicExponent, ksssPowerRawVarianceExponent]
    omega
  have hn : t ^ (2 * s + b + 1) ≤ n := (pow_le_pow_right₀ ht hgap).trans hscale
  calc
    _ ≤ n / (384 * t ^ (2 * s + b)) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 384) (by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hn (by norm_num : (0 : ℝ) ≤ 384)
      rw [pow_succ] at hm
      nlinarith only [hm]
    _ = (1 / (24 * t ^ s)) ^ 2 * ((24 / t ^ b) * n) / 16 := by
      rw [pow_add, pow_mul]
      field_simp
      ring
    _ ≤ _ := by gcongr

theorem source_regularized_stopping_mass
    (q b B k Rmin c : ℕ) (n t E : ℝ) (ht : 3 ≤ t) (hcb : c ≤ b)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ n)
    (hE : n ^ 2 / t ^ b ≤ E) : 3 * t ^ c ≤ E := by
  let R := ksssPowerDenominatorExponent q b B k Rmin
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hgap : c + 1 + b ≤ 2 * R := by
    dsimp only [R, ksssPowerDenominatorExponent, ksssPowerThetaExponent,
      ksssPowerJumpExponent, ksssPowerVarianceExponent, ksssPowerMarginExponent,
      ksssPowerErrorExponent, ksssPowerDeterministicExponent, ksssPowerRawVarianceExponent]
    omega
  calc
    _ ≤ t ^ (c + 1) := by simpa only [pow_succ, mul_comm] using
      mul_le_mul_of_nonneg_right ht (pow_nonneg ht0.le c)
    _ ≤ n ^ 2 / t ^ b := by
      apply (le_div_iff₀ (pow_pos ht0 b)).mpr
      rw [← pow_add]
      calc
        _ ≤ t ^ (2 * R) := pow_le_pow_right₀ ht1 hgap
        _ = (t ^ R) ^ 2 := by rw [← pow_mul]; congr 1; omega
        _ ≤ n ^ 2 := pow_le_pow_left₀ (pow_nonneg ht0.le _) hscale _
    _ ≤ E := hE

theorem eventually_source_regularized_sampling_success
    (q b B k Rmin ambientPower : ℕ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ (n p eta : ℝ),
      (t : ℝ) ^ ksssPowerDenominatorExponent q b B k Rmin ≤ n →
      n ≤ (t : ℝ) ^ ambientPower → 24 / (t : ℝ) ^ b ≤ p ^ 2 * eta →
      2 * n ^ 2 * Real.exp
        (-(1 / (24 * (t : ℝ) ^ ksssPowerErrorExponent b B)) ^ 2 * (p ^ 2 * eta * n) / 16) < 1 := by
  obtain ⟨T, hT1, hT⟩ := eventually_polynomial_exp_neg_mul_lt 2 (1 / 384) 1 (2 * ambientPower)
    (by norm_num) (by norm_num)
  refine ⟨T, hT1, ?_⟩
  intro t ht n p eta hnLower hnUpper hdensity
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast hT1.trans ht
  have hn : 0 ≤ n := (pow_nonneg (by positivity : (0 : ℝ) ≤ t) _).trans hnLower
  have hscale := source_regularized_sampling_exponent q b B k Rmin n t p eta ht1 hnLower hdensity
  have hexp : Real.exp
      (-(1 / (24 * (t : ℝ) ^ ksssPowerErrorExponent b B)) ^ 2 * (p ^ 2 * eta * n) / 16) ≤
        Real.exp (-(1 / 384 : ℝ) * t) := by
    apply Real.exp_le_exp.mpr
    linarith only [hscale]
  have hn2 : n ^ 2 ≤ (t : ℝ) ^ (2 * ambientPower) := by
    simpa only [← pow_mul, Nat.mul_comm ambientPower 2] using pow_le_pow_left₀ hn hnUpper 2
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hn2 (by norm_num)) hexp
    (Real.exp_pos _).le (by positivity)).trans_lt (hT t ht)

end Erdos207
