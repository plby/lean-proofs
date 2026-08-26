/- Adapted from the checked repository proof in Erdos1148/PrimePowerConvolution.lean. -/
import ErdosProblems.Erdos941.RealZetaConvolution

/-! # Local congruences of arithmetic functions at powers of one prime -/

namespace Erdos941.Analytic

open ArithmeticFunction Finset

theorem convolution_prime_power_congr {R : Type*} [Semiring R] {p : ℕ} (hp : p.Prime)
    {f f' g g' : ArithmeticFunction R}
    (hf : ∀ k : ℕ, f (p ^ k) = f' (p ^ k))
    (hg : ∀ k : ℕ, g (p ^ k) = g' (p ^ k)) (k : ℕ) :
    (f * g) (p ^ k) = (f' * g') (p ^ k) := by
  rw [mul_apply, mul_apply]
  apply sum_congr rfl
  intro u hu
  have huEq := (Nat.mem_divisorsAntidiagonal.mp hu).1
  have hu1 : u.1 ∣ p ^ k := ⟨u.2, huEq.symm⟩
  have hu2 : u.2 ∣ p ^ k := ⟨u.1, by rw [mul_comm]; exact huEq.symm⟩
  obtain ⟨i, hi, hui⟩ := (Nat.dvd_prime_pow hp).mp hu1
  obtain ⟨j, hj, huj⟩ := (Nat.dvd_prime_pow hp).mp hu2
  rw [hui, huj, hf, hg]

theorem arithmetic_convolution_nonneg {f g : ArithmeticFunction ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f * g) n := by
  rw [mul_apply]
  exact sum_nonneg (fun u _ => mul_nonneg (hf u.1) (hg u.2))

lemma realCharacterArithmetic_prime_pow {q p : ℕ} (χ : DirichletCharacter ℝ q)
    (hp : p.Prime) (k : ℕ) : realCharacterArithmetic χ (p ^ k) = χ p ^ k := by
  rw [realCharacterArithmetic, ← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero k hp.ne_zero),
    Nat.cast_pow, map_pow]

lemma arithmetic_zeta_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (zeta : ArithmeticFunction ℝ) (p ^ k) = 1 := by
  simp only [natCoe_apply, zeta_apply, pow_ne_zero k hp.ne_zero, if_false, Nat.cast_one]

lemma arithmetic_one_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ArithmeticFunction ℝ) (p ^ k) = (0 : ℝ) ^ k := by
  cases k with
  | zero => simp
  | succ k =>
    have hne : p ^ (k + 1) ≠ 1 := (one_lt_pow' hp.one_lt (Nat.succ_ne_zero k)).ne'
    simp only [one_apply, hne, if_false, zero_pow (Nat.succ_ne_zero k)]

lemma realCharacterArithmetic_pmul_prime_pow {q r p : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (hp : p.Prime) (k : ℕ) :
    ((realCharacterArithmetic χ).pmul (realCharacterArithmetic ψ)) (p ^ k) =
      (χ p * ψ p) ^ k := by
  rw [pmul_apply, realCharacterArithmetic_prime_pow χ hp,
    realCharacterArithmetic_prime_pow ψ hp, mul_pow]

end Erdos941.Analytic
