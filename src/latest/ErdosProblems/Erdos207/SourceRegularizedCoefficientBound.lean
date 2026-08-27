/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizedInitialDegree

/-! # Sparse-stage degree cutoffs give fixed, not growing, trajectory coefficients -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem sparse_degree_power_budget (d : ℕ) (t p tau : ℝ≥0)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hsmall : t * p ≤ tau) :
    t * p ^ d ≤ tau ^ d := by
  have htpow : t ≤ t ^ d := by simpa only [pow_one] using pow_le_pow_right₀ ht hd
  calc
    _ ≤ t ^ d * p ^ d := mul_le_mul_of_nonneg_right htpow zero_le
    _ = (t * p) ^ d := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left' hsmall d

theorem source_regularized_degree_scale_bound (d : ℕ) (t p tau n C ratio : ℝ≥0)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hsmall : t * p ≤ tau)
    (hratio : p ^ 2 * tau * n / 24 ≤ ratio) :
    9 * t * C * (p ^ 3 * n) ^ d ≤ (9 * C * 24 ^ d) * ratio ^ d := by
  have hpower := sparse_degree_power_budget d t p tau hd ht hsmall
  have hbase : p ^ 2 * tau * n ≤ 24 * ratio := by
    have h := (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 24)).1 hratio
    simpa only [mul_comm ratio 24] using h
  calc
    _ = (9 * C) * (t * p ^ d) * (p ^ 2 * n) ^ d := by ring
    _ ≤ (9 * C) * tau ^ d * (p ^ 2 * n) ^ d := by gcongr
    _ = (9 * C) * (p ^ 2 * tau * n) ^ d := by ring
    _ ≤ (9 * C) * (24 * ratio) ^ d := mul_le_mul_of_nonneg_left (pow_le_pow_left' hbase d) zero_le
    _ = _ := by rw [mul_pow]; ring

theorem regularizedTrajectoryCoefficient_source_bound
    {I : Type*} [Fintype I] [DecidableEq I] (Lstar : ℕ → Finset (Finset I))
    (A E : ℝ) (d : ℕ) (t p tau n C : ℝ≥0) (hA : 0 < A) (hE : 0 < E)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hsmall : t * p ≤ tau)
    (hratio : (p : ℝ) ^ 2 * tau * n / 24 ≤ A / E)
    (hdegree : (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ≥0) ≤ 9 * t * C * (p ^ 3 * n) ^ d) :
    regularizedTrajectoryCoefficient Lstar A d * E ^ d ≤ (9 * (C : ℝ) * 24 ^ d) := by
  let ratio : ℝ≥0 := ⟨A / E, (div_pos hA hE).le⟩
  have hr : p ^ 2 * tau * n / 24 ≤ ratio := by exact_mod_cast hratio
  have hbound := hdegree.trans (source_regularized_degree_scale_bound d t p tau n C ratio hd ht hsmall hr)
  apply regularizedTrajectoryCoefficient_scaled_le Lstar A E (9 * (C : ℝ) * 24 ^ d) d hA hE
  exact_mod_cast hbound

theorem regularized_density_power_floors (n t p tau : ℝ≥0) (b : ℕ) (ht : 1 ≤ t)
    (hedge : 8 ≤ p * t ^ b) (hratio : 24 ≤ p ^ 2 * tau * t ^ b) :
    n ^ 2 / t ^ b ≤ p * n ^ 2 / 8 ∧ n / t ^ b ≤ p ^ 2 * tau * n / 24 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  constructor
  · apply (div_le_div_iff₀ (pow_pos ht0 b) (by norm_num : (0 : ℝ≥0) < 8)).2
    have h := mul_le_mul_of_nonneg_right hedge (show 0 ≤ n ^ 2 from zero_le)
    nlinarith only [h]
  · apply (div_le_div_iff₀ (pow_pos ht0 b) (by norm_num : (0 : ℝ≥0) < 24)).2
    have h := mul_le_mul_of_nonneg_right hratio (show 0 ≤ n from zero_le)
    nlinarith only [h]

end

end Erdos207
