import ErdosProblems.Erdos421.FiniteDirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Choose.Sum

/-! # Divisor tuples and bounds for convolution coefficients -/

namespace Erdos421

noncomputable def divisorTuples (k n : ℕ) : ℕ :=
  (ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n

theorem divisorTuples_zero (n : ℕ) : divisorTuples 0 n = if n = 1 then 1 else 0 := by
  simp only [divisorTuples, pow_zero, ArithmeticFunction.one_apply]

theorem divisorTuples_succ (k n : ℕ) :
    divisorTuples (k + 1) n = ∑ d ∈ n.divisors, divisorTuples k d := by
  simp only [divisorTuples, pow_succ, ArithmeticFunction.mul_zeta_apply]

theorem divisorTuples_succ_antidiagonal (k n : ℕ) :
    divisorTuples (k + 1) n = ∑ p ∈ n.divisorsAntidiagonal, divisorTuples k p.1 := by
  simp only [divisorTuples, pow_succ, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ArithmeticFunction.zeta_apply_ne (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).2, mul_one]

theorem norm_convolution_pow_le (f : ArithmeticFunction ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ C) (k n : ℕ) :
    ‖(f ^ k : ArithmeticFunction ℂ) n‖ ≤ C ^ k * divisorTuples k n := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, divisorTuples_zero]
    by_cases hn : n = 1 <;> simp [hn]
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    calc
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
          ‖(f ^ k : ArithmeticFunction ℂ) p.1 * f p.2‖ := norm_sum_le _ _
      _ = ∑ p ∈ n.divisorsAntidiagonal, ‖(f ^ k : ArithmeticFunction ℂ) p.1‖ * ‖f p.2‖ := by
        simp only [norm_mul]
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal, (C ^ k * divisorTuples k p.1) * C := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul (ih p.1) (hf p.2 (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).2)
          (norm_nonneg _) (mul_nonneg (pow_nonneg hC _) (Nat.cast_nonneg _))
      _ = ∑ p ∈ n.divisorsAntidiagonal, C ^ (k + 1) * divisorTuples k p.1 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [pow_succ]
        ring
      _ = _ := by rw [divisorTuples_succ_antidiagonal, Nat.cast_sum, Finset.mul_sum]

theorem divisorTuples_prime_pow {p : ℕ} (hp : p.Prime) (k e : ℕ) :
    divisorTuples k (p ^ e) = k.multichoose e := by
  induction k generalizing e with
  | zero =>
    cases e with
    | zero => simp [divisorTuples_zero]
    | succ e =>
      simp [divisorTuples_zero, hp.ne_one]
  | succ k ih =>
    rw [divisorTuples_succ, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
    have heq : k + 1 + e - 1 = e + k := by omega
    rw [heq]
    exact Nat.choose_symm_of_eq_add (by omega)

end Erdos421
