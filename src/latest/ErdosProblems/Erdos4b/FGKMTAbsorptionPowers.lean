/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTStageErrorEnvelope

/-! # Integer-power inequalities for uniform covering error absorption -/

namespace Erdos4b.FGKMT

theorem absorption_parameter_le_one {S z : ℝ} (hS : 1 ≤ S) (hz : 0 ≤ z)
    (hsmall : S ^ 3 * z ≤ 1) : z ≤ 1 := by
  have hp : 1 ≤ S ^ 3 := one_le_pow₀ hS
  nlinarith

theorem absorption_scaled_power_le_one {S z : ℝ} (hS : 1 ≤ S) (hz : 0 ≤ z)
    (hsmall : S ^ 3 * z ≤ 1) {a b : ℕ} (hab : a ≤ 3 * b) :
    S ^ a * z ^ b ≤ 1 := by
  calc
    _ ≤ S ^ (3 * b) * z ^ b := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hS hab) (pow_nonneg hz _)
    _ = (S ^ 3 * z) ^ b := by rw [mul_pow, ← pow_mul]
    _ ≤ 1 := pow_le_one₀ (mul_nonneg (pow_nonneg (by linarith) _) hz) hsmall

theorem absorption_scaled_power_le {S z : ℝ} (hS : 1 ≤ S) (hz : 0 ≤ z)
    (hsmall : S ^ 3 * z ≤ 1) {a b c : ℕ} (hbc : c ≤ b) (hab : a ≤ 3 * (b - c)) :
    S ^ a * z ^ b ≤ z ^ c := by
  have hp := absorption_scaled_power_le_one hS hz hsmall hab
  calc
    _ = (S ^ a * z ^ (b - c)) * z ^ c := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hbc]
    _ ≤ 1 * z ^ c := mul_le_mul_of_nonneg_right hp (pow_nonneg hz _)
    _ = _ := one_mul _

theorem absorption_scaled_power_le_div {S z : ℝ} (hS : 1 ≤ S) (hz : 0 ≤ z)
    (hsmall : S ^ 3 * z ≤ 1) {a b c : ℕ} (hab : a + c ≤ 3 * b) :
    S ^ a * z ^ b ≤ 1 / S ^ c := by
  have hpos : 0 < S := by linarith
  apply (le_div_iff₀ (pow_pos hpos c)).mpr
  calc
    _ = S ^ (a + c) * z ^ b := by rw [pow_add]; ring
    _ ≤ 1 := absorption_scaled_power_le_one hS hz hsmall hab

theorem absorption_power_antitone {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    {a b : ℕ} (hab : a ≤ b) : z ^ b ≤ z ^ a :=
  pow_le_pow_of_le_one hz0 hz1 hab

theorem absorption_half_bounds {S z : ℝ} (hS : 256 ≤ S) (hz : 0 ≤ z)
    (hsmall : S ^ 3 * z ≤ 1) : z ^ 30 ≤ 1 / 2 ∧ z ^ 10 ≤ 1 / 2 := by
  have hS1 : 1 ≤ S := by linarith
  have hz1 := absorption_parameter_le_one hS1 hz hsmall
  have hzdiv : z ≤ 1 / S := by
    simpa only [pow_zero, one_mul, pow_one] using
      (absorption_scaled_power_le_div hS1 hz hsmall (a := 0) (b := 1) (c := 1) (by omega))
  have hhalf : 1 / S ≤ (1 : ℝ) / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  constructor
  · exact (absorption_power_antitone hz hz1 (a := 1) (b := 30) (by omega)).trans
      (by simpa only [pow_one] using hzdiv.trans hhalf)
  · exact (absorption_power_antitone hz hz1 (a := 1) (b := 10) (by omega)).trans
      (by simpa only [pow_one] using hzdiv.trans hhalf)

theorem absorption_final_error {S z : ℝ} (hS : 256 ≤ S) (hz : 0 ≤ z)
    (hsmall : S ^ 3 * z ≤ 1) : 139 * S ^ 5 * z ^ 5 ≤ z ^ 3 := by
  have hS1 : 1 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hpow := absorption_scaled_power_le_div hS1 hz hsmall
    (a := 5) (b := 2) (c := 1) (by omega)
  have hfactor : 139 * (S ^ 5 * z ^ 2) ≤ 1 := by
    calc
      _ ≤ 139 * (1 / S) := mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hpow)
        (by norm_num)
      _ ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hSpos).mpr (by linarith)
  calc
    _ = (139 * (S ^ 5 * z ^ 2)) * z ^ 3 := by ring
    _ ≤ 1 * z ^ 3 := mul_le_mul_of_nonneg_right hfactor (pow_nonneg hz _)
    _ = _ := one_mul _

theorem absorption_monomial_mono {S z : ℝ} (hS : 1 ≤ S) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    {a b c d : ℕ} (hac : a ≤ c) (hdb : d ≤ b) :
    S ^ a * z ^ b ≤ S ^ c * z ^ d :=
  mul_le_mul (pow_le_pow_right₀ hS hac) (absorption_power_antitone hz0 hz1 hdb)
    (pow_nonneg hz0 _) (pow_nonneg (by linarith) _)

theorem absorption_hit_small {S z : ℝ} (hS : 256 ≤ S) (hz : 0 ≤ z)
    (hsmall : S ^ 3 * z ≤ 1) : 2 * S ^ 2 * z ^ 60 ≤ 1 / 2 := by
  have hS1 : 1 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hp := absorption_scaled_power_le_div hS1 hz hsmall
    (a := 2) (b := 60) (c := 1) (by omega)
  calc
    _ = 2 * (S ^ 2 * z ^ 60) := by ring
    _ ≤ 2 * (1 / S) := mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hp)
      (by norm_num)
    _ = 2 / S := by ring
    _ ≤ 1 / 2 := (div_le_iff₀ hSpos).mpr (by linarith)

theorem absorption_product_small {S z : ℝ} (hS : 256 ≤ S) (hz : 0 ≤ z)
    (hsmall : S ^ 3 * z ≤ 1) :
    8 * S ^ 4 * z ^ 120 + 2 * S * z ^ 5 + 2 * S ^ 3 * z ^ 60 ≤ 1 := by
  have hS1 : 1 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have h1 := absorption_scaled_power_le_div hS1 hz hsmall
    (a := 4) (b := 120) (c := 1) (by omega)
  have h2 := absorption_scaled_power_le_div hS1 hz hsmall
    (a := 1) (b := 5) (c := 1) (by omega)
  have h3 := absorption_scaled_power_le_div hS1 hz hsmall
    (a := 3) (b := 60) (c := 1) (by omega)
  have h12 : 12 / S ≤ 1 := (div_le_one hSpos).mpr (by linarith)
  have h12' : 12 * (1 / S) ≤ 1 := by simpa only [mul_one_div] using h12
  simp only [pow_one] at h1 h2 h3
  linarith only [h1, h2, h3, h12']

theorem absorption_error_polynomial {S z : ℝ} (hS : 1 ≤ S) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    16 * S ^ 4 * z ^ 120 + 4 * S * z ^ 5 + 4 * S ^ 3 * z ^ 60 +
      31 * S ^ 3 * z ^ 20 + 14 * S ^ 4 * z ^ 5 ≤ 69 * S ^ 4 * z ^ 5 := by
  have h1 := absorption_monomial_mono hS hz hz1 (a := 4) (b := 120) (c := 4) (d := 5)
    (by omega) (by omega)
  have h2 := absorption_monomial_mono hS hz hz1 (a := 1) (b := 5) (c := 4) (d := 5)
    (by omega) (by omega)
  have h3 := absorption_monomial_mono hS hz hz1 (a := 3) (b := 60) (c := 4) (d := 5)
    (by omega) (by omega)
  have h4 := absorption_monomial_mono hS hz hz1 (a := 3) (b := 20) (c := 4) (d := 5)
    (by omega) (by omega)
  simp only [pow_one] at h2
  linarith

end Erdos4b.FGKMT
