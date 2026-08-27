/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerAmbientBudgets
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Explicit exponential-parameter choice for dimension-scaled concentration -/

namespace Erdos207

noncomputable section

def powerConcentrationTheta (N t : ℝ) (z H : ℕ) : ℝ := 1 / (N ^ z * t ^ H)

theorem powerConcentrationTheta_pos (N t : ℝ) (z H : ℕ) (hN : 0 < N) (ht : 0 < t) :
    0 < powerConcentrationTheta N t z H := by unfold powerConcentrationTheta; positivity

theorem powerConcentrationTheta_jump_le_one
    (N t J : ℝ) (z H j : ℕ) (hN : 0 < N) (ht : 1 ≤ t) (hj : j ≤ H)
    (hJ : J ≤ N ^ z * t ^ j) : powerConcentrationTheta N t z H * J ≤ 1 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hp := powerConcentrationTheta_pos N t z H hN htpos
  calc
    _ ≤ powerConcentrationTheta N t z H * (N ^ z * t ^ H) := by
      apply mul_le_mul_of_nonneg_left _ hp.le
      exact hJ.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hj) (pow_nonneg hN.le z))
    _ = 1 := by unfold powerConcentrationTheta; field_simp

theorem power_concentration_exponent_le_neg_scale
    (N t margin steps variance : ℝ) (R z H m v : ℕ)
    (hN : 1 ≤ N) (ht : 4 ≤ t) (hscale : t ^ R ≤ N)
    (_hsteps0 : 0 ≤ steps) (hsteps : steps ≤ N ^ 2) (hvariance0 : 0 ≤ variance)
    (hvariance : variance ≤ N ^ (2 * z) / N * t ^ v)
    (hmargin : N ^ (z + 1) / (2 * t ^ m) ≤ margin)
    (hH : v + m + 1 ≤ H) (hR : H + m + 2 ≤ R) :
    -powerConcentrationTheta N t z H * margin +
      powerConcentrationTheta N t z H ^ 2 * steps * variance ≤ -t := by
  have hNpos : 0 < N := by linarith
  have htpos : 0 < t := by linarith
  have htheta := powerConcentrationTheta_pos N t z H hNpos htpos
  have hvar : powerConcentrationTheta N t z H ^ 2 * steps * variance ≤
      N * t ^ v / t ^ (2 * H) := by
    calc
      _ ≤ powerConcentrationTheta N t z H ^ 2 * N ^ 2 * (N ^ (2 * z) / N * t ^ v) := by gcongr
      _ = _ := by
        unfold powerConcentrationTheta
        rw [Nat.mul_comm 2 z, pow_mul, Nat.mul_comm 2 H, pow_mul]
        field_simp
  have hfour : 4 * t ^ (v + m) ≤ t ^ H := real_coeff_mul_pow_le_pow (by linarith) ht hH
  have hsmall : N * t ^ v / t ^ (2 * H) ≤ N / (4 * t ^ (H + m)) := by
    rw [div_le_div_iff₀ (pow_pos htpos _) (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hfour (show 0 ≤ N * t ^ H by positivity)
    convert hm using 1 <;> simp only [pow_add, pow_mul, pow_two] <;> ring
  have hmar : N / (2 * t ^ (H + m)) ≤ powerConcentrationTheta N t z H * margin := by
    calc
      _ = powerConcentrationTheta N t z H * (N ^ (z + 1) / (2 * t ^ m)) := by
        unfold powerConcentrationTheta
        rw [pow_add, pow_succ]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmargin htheta.le
  have hdom : 4 * t ^ (H + m + 1) ≤ N := by
    have h := coeff_power_le_ambient_power_ratio N t 4 R 1 (H + m + 1) 0
      (by linarith) hNpos.le hscale ht (by omega)
    simpa only [pow_one, pow_zero, div_one] using h
  have htime : t ≤ N / (4 * t ^ (H + m)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * t ^ (H + m))).mpr
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hdom
  have hhalf : N / (2 * t ^ (H + m)) = 2 * (N / (4 * t ^ (H + m))) := by ring
  rw [hhalf] at hmar
  have hvar' := hvar.trans hsmall
  nlinarith only [hvar', hmar, htime]

theorem exp_neg_nat_le_half_pow (t : ℕ) : Real.exp (-(t : ℝ)) ≤ (1 / 2 : ℝ) ^ t := by
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h
    exact h
  have hhalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hexp
  have hid : -(t : ℝ) = (t : ℝ) * (-1) := by ring
  rw [hid, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hhalf t

end

end Erdos207
