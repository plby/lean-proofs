/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerAmbientBudgets

/-! # Deterministic power budgets for relative extension concentration -/

namespace Erdos207

theorem pattern_taylor_relative_inverse_clock
    (M f C E t : ℝ) (d s : ℕ) (hM : 0 < M) (hf : 0 < f) (hC : 0 ≤ C)
    (hE : 0 < E) (ht : 0 < t) (hfLower : M / t ^ d ≤ f)
    (hscale : C * t ^ (d + s) ≤ E) :
    (M * C / E ^ 2) / f ≤ 1 / (E * t ^ s) := by
  calc
    _ ≤ (M * C / E ^ 2) / (M / t ^ d) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfLower
    _ = (C * t ^ (d + s)) / (E ^ 2 * t ^ s) := by
      rw [pow_add]
      field_simp
    _ ≤ E / (E ^ 2 * t ^ s) := div_le_div_of_nonneg_right hscale (by positivity)
    _ = _ := by field_simp

theorem pattern_taylor_relative_envelope_budget
    (tau f E L t z : ℝ) (s : ℕ) (hE : 0 < E) (hL : 0 < L) (ht : 1 ≤ t)
    (hLE : L ≤ E) (htau : tau / f ≤ 1 / (E * t ^ s))
    (hz : 4 / t ^ s ≤ 3 * z) :
    4 * tau / f ≤ 3 * z / L ∧ tau / f ≤ 1 / L := by
  have htpos : 0 < t := by linarith
  have hz0 : 0 ≤ 3 * z := (by positivity : 0 ≤ 4 / t ^ s).trans hz
  have hEpower : E ≤ E * t ^ s := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ ht : 1 ≤ t ^ s) hE.le
  constructor
  · calc
      _ = 4 * (tau / f) := by ring
      _ ≤ 4 * (1 / (E * t ^ s)) := mul_le_mul_of_nonneg_left htau (by norm_num)
      _ = (4 / t ^ s) / E := by ring
      _ ≤ (3 * z) / E := div_le_div_of_nonneg_right hz hE.le
      _ ≤ _ := div_le_div_of_nonneg_left hz0 hL hLE
  · calc
      _ ≤ 1 / (E * t ^ s) := htau
      _ ≤ 1 / E := one_div_le_one_div_of_le hE hEpower
      _ ≤ _ := one_div_le_one_div_of_le hL hLE

theorem pattern_selector_size_power_budget
    (N t L e m : ℝ) (R s b : ℕ) (ht : 1 ≤ t) (hN : 0 ≤ N)
    (hscale : t ^ R ≤ N) (hcoeff : 3 * m ≤ t) (hgap : 2 * b + s + 1 ≤ 2 * R)
    (hL : N ^ 2 / t ^ (2 * b) ≤ L) (he : N / t ^ s ≤ e) :
    m * N ≤ L * e / 3 := by
  have htpos : 0 < t := by linarith
  have hsmall := coeff_power_le_ambient_power_ratio N t (3 * m) R 2 0 (2 * b + s)
    ht hN hscale hcoeff (by omega)
  simp only [pow_zero, mul_one] at hsmall
  have hL0 : 0 ≤ L := (by positivity : 0 ≤ N ^ 2 / t ^ (2 * b)).trans hL
  have hmain : 3 * m * N ≤ L * e := by
    calc
      _ ≤ (N ^ 2 / t ^ (2 * b + s)) * N := mul_le_mul_of_nonneg_right hsmall hN
      _ = (N ^ 2 / t ^ (2 * b)) * (N / t ^ s) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul hL he (by positivity) hL0
  linarith only [hmain]

theorem relative_pattern_clock_moments_power_bounds
    (N M f L t J Cj Cv : ℝ) (d b : ℕ)
    (hN : 0 < N) (hM : 0 < M) (ht : 0 < t) (hJ : 0 ≤ J)
    (hf : M / t ^ d ≤ f) (hL : N ^ 2 / t ^ (2 * b) ≤ L)
    (hCj : Cj ≤ t) (hCv : Cv ≤ t) :
    Cj * J / f ≤ t ^ (d + 1) * J / M ∧
      Cv * J / (f * L) ≤ t ^ (d + 2 * b + 1) * J / (M * N ^ 2) := by
  have hfpos : 0 < f := (by positivity : 0 < M / t ^ d).trans_le hf
  have hLpos : 0 < L := (by positivity : 0 < N ^ 2 / t ^ (2 * b)).trans_le hL
  constructor
  · calc
      _ ≤ t * J / f := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCj hJ) hfpos.le
      _ ≤ t * J / (M / t ^ d) := div_le_div_of_nonneg_left (by positivity) (by positivity) hf
      _ = _ := by rw [pow_succ]; field_simp
  · calc
      _ ≤ t * J / (f * L) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCv hJ) (mul_pos hfpos hLpos).le
      _ ≤ t * J / ((M / t ^ d) * (N ^ 2 / t ^ (2 * b))) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul hf hL (by positivity) hfpos.le)
      _ = _ := by simp only [pow_add]; field_simp

end Erdos207
