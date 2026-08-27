/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveRegularizationPowerScalars
import ErdosProblems.Erdos207.PolynomialExponentialDecay

/-! # All reserve-regularization numerical budgets hold eventually at fixed power scales -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem eventually_reserveRegularization_power_budgets
    (b c e a L R : ℕ) (tau0 : ℝ≥0) (epsilon : ℝ)
    (hc : 1 ≤ c) (he : 1 ≤ e) (ha : 4 * b + 1 ≤ a)
    (hLreserve : 4 * b + c + 1 ≤ L) (hLsampling : 2 * b + 2 * e + 1 ≤ L)
    (htau0 : 0 < tau0) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ (n u : ℕ) (p tau : ℝ≥0),
      t ^ L ≤ n → n ≤ t ^ R → 1 / (t : ℝ≥0) ^ b ≤ p → tau0 ≤ tau →
      (u : ℝ≥0) ≤ (n : ℝ≥0) / (t : ℝ≥0) ^ a →
      6144 ≤ p ^ 4 * tau ^ 6 * n ∧
      (u : ℝ≥0) ≤ p ^ 4 * tau ^ 6 * n / 1536 ∧
      (1 / (t : ℝ≥0) ^ c) ≤ 1 / 24576 ∧
      (0 : ℝ) < 1 / (t : ℝ) ^ e ∧ (1 / (t : ℝ) ^ e) ≤ 1 ∧
      2 * (n : ℝ) ^ 2 * Real.exp
        (-(1 / (t : ℝ) ^ e) ^ 2 * ((p : ℝ) ^ 2 * tau * n) / 16) < 1 ∧
      12 * (n + 1 : ℝ) ^ 4 * Real.exp
        (-(1 / (t : ℝ) ^ c) * ((p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * n) / 8) < epsilon := by
  have htauR : (0 : ℝ) < tau0 := by exact_mod_cast htau0
  obtain ⟨TC, hTC⟩ := exists_nat_gt (6144 / (tau0 : ℝ) ^ 6)
  obtain ⟨TS, _hTS1, hTS⟩ := eventually_polynomial_exp_neg_mul_lt 2 ((tau0 : ℝ) / 16) 1
    (2 * R) (by positivity) (by norm_num)
  obtain ⟨TR, _hTR1, hTR⟩ := eventually_polynomial_exp_neg_mul_lt 192 ((tau0 : ℝ) ^ 6 / 8)
    epsilon (4 * R) (by positivity) hepsilon
  let T := max 24576 (max TC (max TS TR))
  refine ⟨T, by dsimp [T]; omega, fun t ht n u p tau hnlo hnhi hp htau hinner ↦ ?_⟩
  have htlarge : 24576 ≤ t := (le_max_left _ _).trans ht
  have htC : TC ≤ t := (le_max_left TC _).trans ((le_max_right _ _).trans ht)
  have htS : TS ≤ t := (le_max_left TS TR).trans
    ((le_max_right TC _).trans ((le_max_right _ _).trans ht))
  have htR : TR ≤ t := (le_max_right TS TR).trans
    ((le_max_right TC _).trans ((le_max_right _ _).trans ht))
  have ht1 : 1 ≤ t := by omega
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have htNN0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have htReal : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have htReal0 : (0 : ℝ) < t := by positivity
  have hnloNN : (t : ℝ≥0) ^ L ≤ n := by exact_mod_cast hnlo
  have hnhiR : (n : ℝ) ≤ (t : ℝ) ^ R := by exact_mod_cast hnhi
  have hcoef : (6144 : ℝ≥0) ≤ tau0 ^ 6 * t := by
    have hTCt : 6144 / (tau0 : ℝ) ^ 6 ≤ t := hTC.le.trans (by exact_mod_cast htC)
    have hCR : (6144 : ℝ) ≤ (tau0 : ℝ) ^ 6 * t := by
      have h := (div_le_iff₀ (pow_pos htauR 6)).mp hTCt
      simpa only [mul_comm] using h
    exact_mod_cast hCR
  have hdensity := hcoef.trans (inversePower_fourth_density_scale t p tau tau0 n b L htNN
    (by omega) hnloNN hp htau)
  have hinner' := inversePower_inner_margin t p tau tau0 n u b a htNN ha hp htau
    ((by norm_num : (1536 : ℝ≥0) ≤ 6144).trans hcoef) hinner
  have hreserve : (1 / (t : ℝ≥0) ^ c) ≤ 1 / 24576 := by
    apply (inversePower_parameter_le_one_div t c htNN hc).trans
    exact div_le_div_of_nonneg_left zero_le (by norm_num) (by exact_mod_cast htlarge)
  have heta0 : (0 : ℝ) < 1 / (t : ℝ) ^ e := by positivity
  have heta1 : (1 / (t : ℝ) ^ e) ≤ 1 := div_le_self (by norm_num) (one_le_pow₀ htReal)
  refine ⟨hdensity, hinner', hreserve, heta0, heta1, ?_, ?_⟩
  · have hscaleNN := inversePower_triangle_sampling_exponent_scale t p tau tau0 n b e L htNN
      hLsampling hnloNN hp htau
    have hscale : (tau0 : ℝ) * t ≤ (1 / (t : ℝ) ^ e) ^ 2 * ((p : ℝ) ^ 2 * tau * n) := by
      exact_mod_cast hscaleNN
    have hexp : Real.exp (-(1 / (t : ℝ) ^ e) ^ 2 * ((p : ℝ) ^ 2 * tau * n) / 16) ≤
        Real.exp (-((tau0 : ℝ) / 16) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hnpow : (n : ℝ) ^ 2 ≤ (t : ℝ) ^ (2 * R) := by
      simpa only [← pow_mul, Nat.mul_comm R 2] using pow_le_pow_left₀ (by positivity) hnhiR 2
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hnpow (by norm_num)) hexp
      (Real.exp_pos _).le (by positivity)).trans_lt (hTS t htS)
  · have hscaleNN := inversePower_reserve_exponent_scale t p tau tau0 n b c L htNN
      hLreserve hnloNN hp htau
    have hscale : (tau0 : ℝ) ^ 6 * t ≤
        (1 / (t : ℝ) ^ c) * ((p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * n) := by exact_mod_cast hscaleNN
    have hexp : Real.exp (-(1 / (t : ℝ) ^ c) * ((p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * n) / 8) ≤
        Real.exp (-((tau0 : ℝ) ^ 6 / 8) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hplus : (n + 1 : ℝ) ≤ 2 * (t : ℝ) ^ R := by
      have hone : (1 : ℝ) ≤ (t : ℝ) ^ R := one_le_pow₀ htReal
      linarith
    have hcoef4 : 12 * (n + 1 : ℝ) ^ 4 ≤ 192 * (t : ℝ) ^ (4 * R) := by
      calc
        _ ≤ 12 * (2 * (t : ℝ) ^ R) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hplus 4) (by norm_num)
        _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm R 4]; ring
    exact (mul_le_mul hcoef4 hexp (Real.exp_pos _).le (by positivity)).trans_lt (hTR t htR)

end

end Erdos207
