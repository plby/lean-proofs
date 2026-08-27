/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerAmbientBudgets

/-! # Retaining the inverse ambient factor in configuration second moments -/

namespace Erdos207

theorem configuration_move_numerator_power
    (N t vprev vcurr alpha beta H : ℝ) (z : ℕ)
    (hN : 0 ≤ N) (ht : 2 ≤ t) (_hvprev : 0 ≤ vprev) (_hvcurr : 0 ≤ vcurr)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hH : 0 ≤ H)
    (hprev : vprev ≤ t * N ^ (z + 2)) (hcurr : vcurr ≤ t * N ^ (z + 1))
    (ha : alpha ≤ t) (hb : beta ≤ t) (hthreat : H ≤ t * N) :
    vprev * alpha + vcurr * (beta * H) ≤ t ^ 4 * N ^ (z + 2) := by
  have ht0 : 0 ≤ t := by linarith
  have hp23 : t ^ 2 ≤ t ^ 3 := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) (by omega)
  have hp34 : 2 * t ^ 3 ≤ t ^ 4 := by
    calc
      _ ≤ t * t ^ 3 := mul_le_mul_of_nonneg_right ht (pow_nonneg ht0 _)
      _ = _ := by ring
  have hpoly : t ^ 2 + t ^ 3 ≤ t ^ 4 := by linarith
  calc
    _ ≤ (t * N ^ (z + 2)) * t + (t * N ^ (z + 1)) * (t * (t * N)) := by gcongr
    _ = (t ^ 2 + t ^ 3) * N ^ (z + 2) := by
      rw [show z + 2 = (z + 1) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpoly (pow_nonneg hN _)

theorem configuration_second_moment_power
    (N t M X R V : ℝ) (z k b : ℕ) (hN : 0 < N) (ht : 6 ≤ t)
    (_hM : 0 ≤ M) (hX : 0 ≤ X)
    (hcutoff : M ≤ N ^ z * t ^ (k + 2))
    (hnum : X ≤ t ^ 4 * N ^ (z + 2))
    (hden : N ^ 3 / (6 * t ^ (5 * b + 1)) ≤ R)
    (hV : V ≤ M * X / R) :
    V ≤ N ^ (2 * z) / N * t ^ (k + 5 * b + 8) := by
  have htpos : 0 < t := by linarith
  have hRpos : 0 < R := (by positivity : (0 : ℝ) < N ^ 3 / (6 * t ^ (5 * b + 1))).trans_le hden
  calc
    V ≤ M * X / R := hV
    _ ≤ (N ^ z * t ^ (k + 2)) * (t ^ 4 * N ^ (z + 2)) /
        (N ^ 3 / (6 * t ^ (5 * b + 1))) := by gcongr
    _ = (N ^ (2 * z) / N) * (6 * t ^ (k + 5 * b + 7)) := by
      simp only [pow_add, pow_mul, pow_succ]
      field_simp
      ring
    _ ≤ (N ^ (2 * z) / N) * t ^ (k + 5 * b + 8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact real_coeff_mul_pow_le_pow (by linarith) ht (by omega)

theorem centered_second_moment_power
    (N t variance A : ℝ) (z r d : ℕ) (hN : 1 ≤ N) (ht : 2 ≤ t) (hA0 : 0 ≤ A)
    (hv : variance ≤ N ^ (2 * z) / N * t ^ r)
    (hA : A ≤ N ^ z / N * t ^ d) :
    2 * variance + 2 * A ^ 2 ≤
      N ^ (2 * z) / N * t ^ (max r (2 * d) + 2) := by
  have hNpos : 0 < N := by linarith
  have htpos : 0 < t := by linarith
  have hNsq : N ≤ N ^ 2 := by nlinarith
  have hAsq : A ^ 2 ≤ N ^ (2 * z) / N * t ^ (2 * d) := by
    calc
      _ ≤ (N ^ z / N * t ^ d) ^ 2 := pow_le_pow_left₀ hA0 hA 2
      _ = N ^ (2 * z) / N ^ 2 * t ^ (2 * d) := by
        simp only [mul_pow, div_pow, ← pow_mul, Nat.mul_comm z 2, Nat.mul_comm d 2]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hNpos hNsq) (by positivity)
  have hr : t ^ r ≤ t ^ max r (2 * d) := pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  have hd : t ^ (2 * d) ≤ t ^ max r (2 * d) := pow_le_pow_right₀ (by linarith) (le_max_right _ _)
  have ht2 : (4 : ℝ) ≤ t ^ 2 := by nlinarith
  have hpoly : 2 * t ^ r + 2 * t ^ (2 * d) ≤ t ^ (max r (2 * d) + 2) := by
    calc
      _ ≤ 4 * t ^ max r (2 * d) := by linarith
      _ ≤ t ^ 2 * t ^ max r (2 * d) := mul_le_mul_of_nonneg_right ht2 (by positivity)
      _ = _ := by rw [pow_add]; ring
  calc
    _ ≤ 2 * (N ^ (2 * z) / N * t ^ r) + 2 * (N ^ (2 * z) / N * t ^ (2 * d)) := by linarith
    _ = (N ^ (2 * z) / N) * (2 * t ^ r + 2 * t ^ (2 * d)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (by positivity)

end Erdos207
