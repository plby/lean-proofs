import ErdosProblems.Erdos1148.BiquadraticConvolution
import ErdosProblems.Erdos1148.DivisorBounds

/-! # Uniform divisor bounds for character-convolution coefficients -/

namespace Erdos1148.DukeArithmetic

open ArithmeticFunction Finset

theorem arithmetic_convolution_norm_le_card_divisors {f g : ArithmeticFunction ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (n : ℕ) :
    ‖(f * g) n‖ ≤ (n.divisors.card : ℝ) := by
  rw [mul_apply]
  calc
    _ ≤ ∑ u ∈ n.divisorsAntidiagonal, ‖f u.1 * g u.2‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply sum_le_sum
      intro u hu
      rw [norm_mul]
      exact (mul_le_mul (hf _) (hg _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, mul_one]
      rw [← Nat.map_div_left_divisors, card_map]

lemma realCharacterArithmetic_norm_le_one {q : ℕ} (χ : DirichletCharacter ℝ q) (n : ℕ) :
    ‖realCharacterArithmetic χ n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, norm_zero, zero_le_one]
  · rw [realCharacterArithmetic, ← χ.apply_eq_toArithmeticFunction_apply hn]
    exact χ.norm_le_one _

lemma arithmetic_zeta_norm_le_one (n : ℕ) : ‖(zeta : ArithmeticFunction ℝ) n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, norm_zero, zero_le_one]
  · simp only [natCoe_apply, zeta_apply, hn, if_false, Nat.cast_one, norm_one, le_refl]

theorem realZetaConvolution_norm_le_card_divisors {q : ℕ}
    (χ : DirichletCharacter ℝ q) (n : ℕ) :
    ‖realZetaConvolution χ n‖ ≤ (n.divisors.card : ℝ) :=
  arithmetic_convolution_norm_le_card_divisors arithmetic_zeta_norm_le_one
    (realCharacterArithmetic_norm_le_one χ) n

theorem realCharacterConvolution_norm_le_card_divisors {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (n : ℕ) :
    ‖(realCharacterArithmetic χ * realCharacterArithmetic ψ) n‖ ≤ (n.divisors.card : ℝ) :=
  arithmetic_convolution_norm_le_card_divisors (realCharacterArithmetic_norm_le_one χ)
    (realCharacterArithmetic_norm_le_one ψ) n

end Erdos1148.DukeArithmetic
