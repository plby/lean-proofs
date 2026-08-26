/- Adapted from the checked repository proof in Erdos1148/CoprimeZetaConvolution.lean. -/
import ErdosProblems.Erdos941.PrimePowerConvolution

/-! # Removing the primes in the character modulus from a zeta convolution -/

namespace Erdos941.Analytic

open ArithmeticFunction Finset

noncomputable def realCoprimeZetaConvolution {q : ℕ} (χ : DirichletCharacter ℝ q) :
    ArithmeticFunction ℝ :=
  realCharacterArithmetic (1 : DirichletCharacter ℝ q) * realCharacterArithmetic χ

lemma realCoprimeZetaConvolution_eq_pmul {q : ℕ} (χ : DirichletCharacter ℝ q) :
    realCoprimeZetaConvolution χ =
      (realCharacterArithmetic (1 : DirichletCharacter ℝ q)).pmul (realZetaConvolution χ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, pmul_apply, zero_mul]
  rw [realCoprimeZetaConvolution, mul_apply, pmul_apply, realZetaConvolution, mul_apply,
    mul_sum]
  apply sum_congr rfl
  intro u hu
  have huEq := (Nat.mem_divisorsAntidiagonal.mp hu).1
  have hu0 : u.1 * u.2 ≠ 0 := huEq ▸ hn
  have h1 := left_ne_zero_of_mul hu0
  have h2 := right_ne_zero_of_mul hu0
  simp only [realCharacterArithmetic,
    ← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ h1,
    ← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ h2,
    ← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ hn,
    natCoe_apply, zeta_apply, h1, if_false, Nat.cast_one, one_mul]
  rw [← huEq, Nat.cast_mul, map_mul]
  have hfix : (1 : DirichletCharacter ℝ q) u.2 * χ u.2 = χ u.2 := by
    change ((1 : DirichletCharacter ℝ q) * χ) u.2 = χ u.2
    rw [one_mul]
  rw [mul_assoc, hfix]

lemma realCoprimeZetaConvolution_apply {q : ℕ} (χ : DirichletCharacter ℝ q)
    {n : ℕ} (hn : n ≠ 0) :
    realCoprimeZetaConvolution χ n =
      (1 : DirichletCharacter ℝ q) n * realZetaConvolution χ n := by
  rw [realCoprimeZetaConvolution_eq_pmul, pmul_apply, realCharacterArithmetic,
    ← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ hn]

lemma realCoprimeZetaConvolution_nonneg {q : ℕ} (χ : DirichletCharacter ℝ q) (n : ℕ) :
    0 ≤ realCoprimeZetaConvolution χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  rw [realCoprimeZetaConvolution_apply χ hn]
  apply mul_nonneg _ (realZetaConvolution_nonneg χ n)
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    exact zero_le_one
  · rw [MulChar.map_nonunit _ hu]

lemma isMultiplicative_realCoprimeZetaConvolution {q : ℕ} (χ : DirichletCharacter ℝ q) :
    (realCoprimeZetaConvolution χ).IsMultiplicative :=
  (1 : DirichletCharacter ℝ q).isMultiplicative_toArithmeticFunction.mul
    χ.isMultiplicative_toArithmeticFunction

lemma realZetaConvolution_prime_pow {q p : ℕ} (χ : DirichletCharacter ℝ q)
    (hp : p.Prime) (k : ℕ) :
    realZetaConvolution χ (p ^ k) = ∑ i ∈ range (k + 1), χ p ^ i := by
  rw [realZetaConvolution, coe_zeta_mul_apply, Nat.divisors_prime_pow hp]
  simp only [sum_map, Function.Embedding.coeFn_mk, realCharacterArithmetic_prime_pow χ hp]

end Erdos941.Analytic
