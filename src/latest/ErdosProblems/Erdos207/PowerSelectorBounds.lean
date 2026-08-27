/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerAmbientBudgets

/-! # Selector floors and dimension-scaled quotients in the coupled process -/

namespace Erdos207

theorem selector_power_lower
    (N t L x R : ℝ) (b : ℕ) (hN : 0 ≤ N) (ht : 0 < t)
    (hL : N ^ 2 / t ^ (2 * b) ≤ L) (hx : N / t ^ (3 * b + 1) ≤ x)
    (hR : L * x / 6 ≤ R) : N ^ 3 / (6 * t ^ (5 * b + 1)) ≤ R := by
  have hL0 : 0 ≤ L := (div_nonneg (sq_nonneg N) (pow_nonneg ht.le _)).trans hL
  have hprod := mul_le_mul hL hx (by positivity) hL0
  calc
    _ = ((N ^ 2 / t ^ (2 * b)) * (N / t ^ (3 * b + 1))) / 6 := by
      have hexp : 5 * b + 1 = 2 * b + (3 * b + 1) := by omega
      rw [hexp, pow_add]
      field_simp
    _ ≤ L * x / 6 := div_le_div_of_nonneg_right hprod (by norm_num)
    _ ≤ R := hR

theorem move_numerator_div_selector_power
    (N t X R : ℝ) (z b : ℕ) (hN : 0 < N) (ht : 6 ≤ t) (_hX : 0 ≤ X)
    (hnum : X ≤ t ^ 4 * N ^ (z + 2))
    (hden : N ^ 3 / (6 * t ^ (5 * b + 1)) ≤ R) :
    X / R ≤ N ^ z / N * t ^ (5 * b + 6) := by
  have htpos : 0 < t := by linarith
  calc
    _ ≤ (t ^ 4 * N ^ (z + 2)) / (N ^ 3 / (6 * t ^ (5 * b + 1))) := by gcongr
    _ = (N ^ z / N) * (6 * t ^ (5 * b + 5)) := by
      simp only [pow_mul, pow_succ]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (real_coeff_mul_pow_le_pow (by linarith) ht (by omega)) (by positivity)

theorem coefficient_envelope_div_clock_power
    (N t X C L : ℝ) (z b : ℕ) (hN : 0 < N) (ht : 0 < t) (hX : 0 ≤ X) (_hC : 0 ≤ C)
    (hnum : X ≤ N ^ (z + 1)) (hcoeff : C ≤ t) (hden : N ^ 2 / t ^ (2 * b) ≤ L) :
    C * X / L ≤ N ^ z / N * t ^ (2 * b + 1) := by
  calc
    _ ≤ t * N ^ (z + 1) / (N ^ 2 / t ^ (2 * b)) := by gcongr
    _ = _ := by
      simp only [pow_succ]
      field_simp

end Erdos207
