/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTriangleRegularization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform asymptotic failure budget for source triangle regularization -/

namespace Erdos207

open Finset Filter
open scoped Topology

noncomputable section

theorem triangleRegularization_density_scale
    (n p : ℝ) (hn : 0 < n) (hp : n ^ (-1 / 6 : ℝ) ≤ p) :
    n ^ (1 / 6 : ℝ) ≤ (n ^ (-1 / 4 : ℝ)) ^ 2 * (p ^ 2 * n) := by
  have hr : 0 < n ^ (-1 / 6 : ℝ) := Real.rpow_pos_of_pos hn _
  have hsq : (n ^ (-1 / 6 : ℝ)) ^ 2 ≤ p ^ 2 := by nlinarith
  have heq : (n ^ (-1 / 4 : ℝ)) ^ 2 * ((n ^ (-1 / 6 : ℝ)) ^ 2 * n) =
      n ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_natCast (n ^ (-1 / 4 : ℝ)) 2,
      ← Real.rpow_natCast (n ^ (-1 / 6 : ℝ)) 2,
      ← Real.rpow_mul hn.le, ← Real.rpow_mul hn.le]
    nth_rw 3 [← Real.rpow_one n]
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1
    norm_num
  rw [← heq]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hn.le) (sq_nonneg _)

theorem triangleRegularization_failure_tendsToZero :
    Tendsto (fun n : ℝ ↦ 2 * n ^ 2 * Real.exp (-n ^ (1 / 6 : ℝ) / 16))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 12 (1 / 16)
    (by norm_num)).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6))
  have hmul := h.const_mul 2
  simp only [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with n hn
  change 2 * ((n ^ (1 / 6 : ℝ)) ^ (12 : ℝ) *
    Real.exp (-(1 / 16) * n ^ (1 / 6 : ℝ))) = _
  rw [← Real.rpow_mul hn]
  norm_num only [show (1 / 6 : ℝ) * 12 = 2 by norm_num, Real.rpow_two]
  have hexp : -(1 / 16 : ℝ) * n ^ (1 / 6 : ℝ) = -n ^ (1 / 6 : ℝ) / 16 := by ring
  rw [hexp]
  ring

theorem exists_triangleRegularization_failure_threshold :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : ℝ,
      (n : ℝ) ^ (-1 / 6 : ℝ) ≤ p →
      2 * (n : ℝ) ^ 2 * Real.exp
        (-((n : ℝ) ^ (-1 / 4 : ℝ)) ^ 2 * (p ^ 2 * n) / 16) < 1 := by
  have ht := triangleRegularization_failure_tendsToZero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ (1 / 6 : ℝ)) / 16) < 1 :=
    ht.eventually_lt_const (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨max N 1, le_max_right _ _, fun n hn p hp ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hscale := triangleRegularization_density_scale n p hnr hp
  apply lt_of_le_of_lt _ (hN n ((le_max_left _ _).trans hn))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  linarith

end

end Erdos207
