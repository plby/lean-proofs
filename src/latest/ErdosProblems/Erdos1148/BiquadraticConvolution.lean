import ErdosProblems.Erdos1148.PrimePowerConvolution

/-! # Positivity of the four-factor real character convolution -/

namespace Erdos1148.DukeArithmetic

open ArithmeticFunction

noncomputable def realBiquadraticConvolution {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) : ArithmeticFunction ℝ :=
  (zeta : ArithmeticFunction ℝ) * realCharacterArithmetic χ * realCharacterArithmetic ψ *
    (realCharacterArithmetic χ).pmul (realCharacterArithmetic ψ)

lemma realBiquadraticConvolution_comm {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) :
    realBiquadraticConvolution χ ψ = realBiquadraticConvolution ψ χ := by
  unfold realBiquadraticConvolution
  rw [pmul_comm (realCharacterArithmetic ψ)]
  ring

lemma realBiquadraticConvolution_prime_pow_of_zero {q r p : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hp : p.Prime)
    (hχp : χ p = 0) (k : ℕ) :
    realBiquadraticConvolution χ ψ (p ^ k) = realZetaConvolution ψ (p ^ k) := by
  have hf : ∀ i : ℕ, realCharacterArithmetic χ (p ^ i) = (1 : ArithmeticFunction ℝ) (p ^ i) := by
    intro i
    rw [realCharacterArithmetic_prime_pow χ hp, arithmetic_one_prime_pow hp, hχp]
  have hh : ∀ i : ℕ, ((realCharacterArithmetic χ).pmul (realCharacterArithmetic ψ)) (p ^ i) =
      (1 : ArithmeticFunction ℝ) (p ^ i) := by
    intro i
    rw [realCharacterArithmetic_pmul_prime_pow χ ψ hp, arithmetic_one_prime_pow hp, hχp, zero_mul]
  have h := convolution_prime_power_congr hp
    (convolution_prime_power_congr hp (g := realCharacterArithmetic ψ)
      (convolution_prime_power_congr hp (f := (zeta : ArithmeticFunction ℝ))
        (fun _ => rfl) hf) (fun _ => rfl)) hh k
  simpa only [realBiquadraticConvolution, realZetaConvolution, mul_one] using h

lemma realBiquadraticConvolution_prime_pow_of_one {q r p : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hp : p.Prime)
    (hχp : χ p = 1) (k : ℕ) :
    realBiquadraticConvolution χ ψ (p ^ k) =
      (realZetaConvolution ψ * realZetaConvolution ψ) (p ^ k) := by
  have hf : ∀ i : ℕ, realCharacterArithmetic χ (p ^ i) =
      (zeta : ArithmeticFunction ℝ) (p ^ i) := by
    intro i
    rw [realCharacterArithmetic_prime_pow χ hp, arithmetic_zeta_prime_pow hp, hχp, one_pow]
  have hh : ∀ i : ℕ, ((realCharacterArithmetic χ).pmul (realCharacterArithmetic ψ)) (p ^ i) =
      realCharacterArithmetic ψ (p ^ i) := by
    intro i
    rw [realCharacterArithmetic_pmul_prime_pow χ ψ hp,
      realCharacterArithmetic_prime_pow ψ hp, hχp, one_mul]
  have h := convolution_prime_power_congr hp
    (convolution_prime_power_congr hp (g := realCharacterArithmetic ψ)
      (convolution_prime_power_congr hp (f := (zeta : ArithmeticFunction ℝ))
        (fun _ => rfl) hf) (fun _ => rfl)) hh k
  change realBiquadraticConvolution χ ψ (p ^ k) =
    ((zeta : ArithmeticFunction ℝ) * zeta * realCharacterArithmetic ψ * realCharacterArithmetic ψ)
      (p ^ k) at h
  rw [h]
  congr 1
  unfold realZetaConvolution
  ring

lemma realBiquadraticConvolution_prime_pow_of_neg_one {q r p : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hp : p.Prime)
    (hχp : χ p = -1) (hψp : ψ p = -1) (k : ℕ) :
    realBiquadraticConvolution χ ψ (p ^ k) =
      (realZetaConvolution χ * realZetaConvolution χ) (p ^ k) := by
  have hg : ∀ i : ℕ, realCharacterArithmetic ψ (p ^ i) = realCharacterArithmetic χ (p ^ i) := by
    intro i
    rw [realCharacterArithmetic_prime_pow ψ hp, realCharacterArithmetic_prime_pow χ hp, hχp, hψp]
  have hh : ∀ i : ℕ, ((realCharacterArithmetic χ).pmul (realCharacterArithmetic ψ)) (p ^ i) =
      (zeta : ArithmeticFunction ℝ) (p ^ i) := by
    intro i
    rw [realCharacterArithmetic_pmul_prime_pow χ ψ hp, arithmetic_zeta_prime_pow hp, hχp, hψp]
    simp only [neg_mul_neg, one_mul, one_pow]
  have h := convolution_prime_power_congr hp
    (convolution_prime_power_congr hp
      (f := (zeta : ArithmeticFunction ℝ) * realCharacterArithmetic χ) (fun _ => rfl) hg) hh k
  change realBiquadraticConvolution χ ψ (p ^ k) =
    ((zeta : ArithmeticFunction ℝ) * realCharacterArithmetic χ * realCharacterArithmetic χ * zeta)
      (p ^ k) at h
  rw [h]
  congr 1
  unfold realZetaConvolution
  ring

theorem realBiquadraticConvolution_prime_pow_nonneg {q r p : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hp : p.Prime) (k : ℕ) :
    0 ≤ realBiquadraticConvolution χ ψ (p ^ k) := by
  rcases realDirichletCharacter_isQuadratic χ p with hχ | hχ | hχ
  · rw [realBiquadraticConvolution_prime_pow_of_zero χ ψ hp hχ]
    exact realZetaConvolution_nonneg ψ _
  · rw [realBiquadraticConvolution_prime_pow_of_one χ ψ hp hχ]
    exact arithmetic_convolution_nonneg
      (realZetaConvolution_nonneg ψ) (realZetaConvolution_nonneg ψ) _
  · rcases realDirichletCharacter_isQuadratic ψ p with hψ | hψ | hψ
    · rw [realBiquadraticConvolution_comm, realBiquadraticConvolution_prime_pow_of_zero ψ χ hp hψ]
      exact realZetaConvolution_nonneg χ _
    · rw [realBiquadraticConvolution_comm, realBiquadraticConvolution_prime_pow_of_one ψ χ hp hψ]
      exact arithmetic_convolution_nonneg
        (realZetaConvolution_nonneg χ) (realZetaConvolution_nonneg χ) _
    · rw [realBiquadraticConvolution_prime_pow_of_neg_one χ ψ hp hχ hψ]
      exact arithmetic_convolution_nonneg
        (realZetaConvolution_nonneg χ) (realZetaConvolution_nonneg χ) _

lemma isMultiplicative_realBiquadraticConvolution {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) :
    (realBiquadraticConvolution χ ψ).IsMultiplicative := by
  have hf := χ.isMultiplicative_toArithmeticFunction
  have hg := ψ.isMultiplicative_toArithmeticFunction
  have hz : (zeta : ArithmeticFunction ℝ).IsMultiplicative := isMultiplicative_zeta.natCast
  exact ((hz.mul hf).mul hg).mul (hf.pmul hg)

theorem realBiquadraticConvolution_nonneg {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (n : ℕ) :
    0 ≤ realBiquadraticConvolution χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact le_of_eq ArithmeticFunction.map_zero.symm
  · rw [(isMultiplicative_realBiquadraticConvolution χ ψ).multiplicative_factorization _ hn]
    exact Finset.prod_nonneg (fun p hp =>
      realBiquadraticConvolution_prime_pow_nonneg χ ψ (Nat.prime_of_mem_primeFactors hp) _)

@[simp] lemma realBiquadraticConvolution_one {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) :
    realBiquadraticConvolution χ ψ 1 = 1 :=
  (isMultiplicative_realBiquadraticConvolution χ ψ).map_one

theorem one_le_weighted_realBiquadraticConvolution {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r)
    (s : ℝ) {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ weightedArithmeticPartialSum (realBiquadraticConvolution χ ψ) s X := by
  have h := Finset.single_le_sum
    (s := Finset.Ioc 0 X)
    (f := fun n : ℕ => (n : ℝ) ^ (-s) * realBiquadraticConvolution χ ψ n)
    (fun n _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (realBiquadraticConvolution_nonneg χ ψ n)) (Finset.mem_Ioc.mpr ⟨zero_lt_one, hX⟩)
  simpa only [Nat.cast_one, Real.one_rpow, realBiquadraticConvolution_one, mul_one,
    weightedArithmeticPartialSum] using h

end Erdos1148.DukeArithmetic
