/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Small primes at which a nonzero polynomial value is invertible.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.PolynomialHeight
import ErdosProblems.Erdos477.Counting.PrimeSelection

namespace Erdos477.Counting

lemma prime_isCoprime_int_of_not_dvd (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) : IsCoprime (p : ℤ) a := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
  exact hp.coprime_iff_not_dvd.mpr (fun h => ha (Int.natCast_dvd.mpr h))

/-- The same absolute constant works for every polynomial, degree, height,
and point. Dependence on the coefficients is explicitly logarithmic. -/
theorem exists_small_prime_for_polynomial_value : ∃ C : ℝ, 0 < C ∧
    ∀ (P : MvPolynomial (Fin 2) ℤ) (D : ℕ), P.totalDegree ≤ D →
    ∀ (z : Fin 2 → ℤ) (B : ℝ), 1 ≤ B → (∀ k, |(z k : ℝ)| ≤ B) →
      MvPolynomial.eval z P ≠ 0 → ∃ p : ℕ, p.Prime ∧
        (p : ℝ) ≤ C * (Real.log (coefficientSum P + 1 : ℕ) + D * Real.log B + 1) ∧
        IsCoprime (p : ℤ) (MvPolynomial.eval z P) := by
  obtain ⟨C, hC, hprime⟩ := exists_small_prime_nondivisor
  refine ⟨C, hC, ?_⟩
  intro P D hD z B hB hz hzero
  obtain ⟨p, hp, hbound, hnot⟩ := hprime (MvPolynomial.eval z P) hzero
  refine ⟨p, hp, ?_, prime_isCoprime_int_of_not_dvd p hp _ hnot⟩
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (by linarith [log_abs_eval_le_coefficientSum P D hD z hzero B hB hz]) hC.le)

#print axioms exists_small_prime_for_polynomial_value
-- 'Erdos477.Counting.exists_small_prime_for_polynomial_value' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
