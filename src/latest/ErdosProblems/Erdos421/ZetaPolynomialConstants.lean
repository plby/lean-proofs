import ErdosProblems.Erdos421.ZetaPolynomialGrowth
import ErdosProblems.Erdos421.StripConstants

/-! # Explicit logarithmic bounds for the polynomial-degree strip constant -/

namespace Erdos421

theorem polynomialZetaStripConstant_le (K : ℕ) :
    polynomialZetaStripConstant K ≤ (2 : ℝ) ^ (1800 * (K + 1) ^ 11) := by
  have hd := polynomialLogarithmicExponent_pos K
  have hd1 : polynomialLogarithmicExponent K ≤ 1 :=
    (polynomialLogarithmicExponent_le_half K).trans (by norm_num)
  have hden := one_sub_two_rpow_neg_half_lower hd hd1
  have hc := polynomialLogarithmicConstant_pos K
  have hpoly : ((K + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (K + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := K + 1)).le
  have hlin : K + 1 ≤ (K + 1) ^ 11 :=
    le_self_pow₀ (by omega : 1 ≤ K + 1) (by decide : 11 ≠ 0)
  have hone : 1 ≤ (K + 1) ^ 11 := Nat.one_le_pow 11 (K + 1) (by omega)
  calc
    _ ≤ polynomialLogarithmicConstant K / (polynomialLogarithmicExponent K / 8) :=
      div_le_div_of_nonneg_left hc.le (by positivity) hden
    _ = (2 : ℝ) ^ (1728 * (K + 1) ^ 11 + 19) * ((K + 1 : ℕ) : ℝ) ^ 3 := by
      unfold polynomialLogarithmicConstant polynomialLogarithmicExponent
      rw [pow_add, div_div_eq_mul_div, div_inv_eq_mul]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      norm_num only [show (2 : ℝ) ^ 19 = 524288 by norm_num]
      generalize (2 : ℝ) ^ (1728 * (K + 1) ^ 11) = C
      ring
    _ ≤ (2 : ℝ) ^ (1728 * (K + 1) ^ 11 + 19) * ((2 : ℝ) ^ (K + 1)) ^ 3 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hpoly 3) (by positivity)
    _ = (2 : ℝ) ^ (1728 * (K + 1) ^ 11 + 19 + (K + 1) * 3) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

theorem polynomialZetaStripConstant_add_sixty_four_le (K : ℕ) :
    polynomialZetaStripConstant K + 64 ≤ (2 : ℝ) ^ (1807 * (K + 1) ^ 11) := by
  have hone : 1 ≤ (2 : ℝ) ^ (1800 * (K + 1) ^ 11) := one_le_pow₀ (by norm_num)
  have hn : 1 ≤ (K + 1) ^ 11 := Nat.one_le_pow 11 (K + 1) (by omega)
  calc
    _ ≤ (2 : ℝ) ^ (1800 * (K + 1) ^ 11) + 64 :=
      add_le_add (polynomialZetaStripConstant_le K) le_rfl
    _ ≤ (2 : ℝ) ^ (1800 * (K + 1) ^ 11 + 7) := by
      rw [pow_add]
      generalize (2 : ℝ) ^ (1800 * (K + 1) ^ 11) = C at hone ⊢
      norm_num only [show (2 : ℝ) ^ 7 = 128 by norm_num]
      linarith
    _ ≤ _ :=
      pow_le_pow_right₀ (by norm_num) (by omega)

end Erdos421
