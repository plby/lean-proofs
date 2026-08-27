/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TriangleRegularizationThreshold

/-! # Uniform density and sampling thresholds for a fixed positive availability density -/

namespace Erdos207

open Filter
open scoped Topology

noncomputable section

theorem triangleRegularization_fourth_density_scale
    (n p : ℝ) (hn : 0 < n) (hp : n ^ (-1 / 6 : ℝ) ≤ p) :
    n ^ (1 / 3 : ℝ) ≤ p ^ 4 * n := by
  have hr : 0 < n ^ (-1 / 6 : ℝ) := Real.rpow_pos_of_pos hn _
  have hpow : (n ^ (-1 / 6 : ℝ)) ^ 4 ≤ p ^ 4 := pow_le_pow_left₀ hr.le hp 4
  have heq : (n ^ (-1 / 6 : ℝ)) ^ 4 * n = n ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast (n ^ (-1 / 6 : ℝ)) 4, ← Real.rpow_mul hn.le]
    nth_rw 2 [← Real.rpow_one n]
    rw [← Real.rpow_add hn]
    congr 1
    norm_num
  rw [← heq]
  exact mul_le_mul_of_nonneg_right hpow hn.le

theorem twoDensityTriangleRegularization_failure_tendsToZero
    (tau0 : ℝ) (htau0 : 0 < tau0) :
    Tendsto (fun n : ℝ ↦ 2 * n ^ 2 * Real.exp (-tau0 * n ^ (1 / 6 : ℝ) / 16))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 12 (tau0 / 16)
    (by positivity)).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6))
  have hmul := h.const_mul 2
  simp only [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with n hn
  change 2 * ((n ^ (1 / 6 : ℝ)) ^ (12 : ℝ) *
    Real.exp (-(tau0 / 16) * n ^ (1 / 6 : ℝ))) = _
  rw [← Real.rpow_mul hn]
  norm_num only [show (1 / 6 : ℝ) * 12 = 2 by norm_num, Real.rpow_two]
  have hexp : -(tau0 / 16) * n ^ (1 / 6 : ℝ) = -tau0 * n ^ (1 / 6 : ℝ) / 16 := by ring
  rw [hexp]
  ring

theorem exists_twoDensityTriangleRegularization_threshold
    (tau0 : ℝ) (htau0 : 0 < tau0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p tau : ℝ,
      (n : ℝ) ^ (-1 / 6 : ℝ) ≤ p → tau0 ≤ tau →
      1536 ≤ p ^ 4 * tau ^ 6 * n ∧
      2 * (n : ℝ) ^ 2 * Real.exp
        (-((n : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 * (p ^ 2 * tau * n) / 16) < 1 := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hnat
  have hdensity : Tendsto (fun n : ℕ ↦ tau0 ^ 6 * (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity : 0 < tau0 ^ 6)).mpr hpow
  have hfail := (twoDensityTriangleRegularization_failure_tendsToZero tau0 htau0).comp hnat
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hdensity.eventually_ge_atTop 1536)
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp (hfail.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨max 1 (max N1 N2), le_max_left _ _, fun n hn p tau hp htau ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbase := triangleRegularization_fourth_density_scale n p hnR hp
  have hτpow : tau0 ^ 6 ≤ tau ^ 6 := pow_le_pow_left₀ htau0.le htau 6
  have hN1n : N1 ≤ n := (le_max_left N1 N2).trans ((le_max_right _ _).trans hn)
  have hN2n : N2 ≤ n := (le_max_right N1 N2).trans ((le_max_right _ _).trans hn)
  constructor
  · calc
      1536 ≤ tau0 ^ 6 * (n : ℝ) ^ (1 / 3 : ℝ) := hN1 n hN1n
      _ ≤ tau0 ^ 6 * (p ^ 4 * n) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ tau ^ 6 * (p ^ 4 * n) := mul_le_mul_of_nonneg_right hτpow (by positivity)
      _ = _ := by ring
  · have hscale := triangleRegularization_density_scale n p hnR hp
    have hscaleτ : tau0 * (n : ℝ) ^ (1 / 6 : ℝ) ≤
        ((n : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 * (p ^ 2 * tau * n) := by
      calc
        _ ≤ tau0 * (((n : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 * (p ^ 2 * n)) :=
          mul_le_mul_of_nonneg_left hscale htau0.le
        _ ≤ tau * (((n : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 * (p ^ 2 * n)) :=
          mul_le_mul_of_nonneg_right htau (by positivity)
        _ = _ := by ring
    apply lt_of_le_of_lt _ (hN2 n hN2n)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith

end

end Erdos207
