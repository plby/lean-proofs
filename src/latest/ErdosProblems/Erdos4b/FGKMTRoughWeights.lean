/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSquarefreeWeights

/-!
# Exact rough squarefree weights

The coefficient definitions and prime-power identities are independent
of the analytic estimates for their moments.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction

/-- The squarefree denominator weight with primes of `M` removed. -/
def roughSieveWeight (M : ℕ) (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  squarefreePrimeWeight (fun p => if p ∣ M then 0 else 1 / g p)

/-- Correction relative to the harmonic function restricted to integers
coprime to `M`. Its local coefficients vanish at every prime of `M`. -/
def roughHarmonicCorrection (M : ℕ) (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  roughSieveWeight M g * squarefreePrimeWeight (fun p => if p ∣ M then 0 else -(1 / (p : ℝ)))

theorem roughHarmonicCorrection_isMultiplicative (M : ℕ) (g : ℕ → ℝ) :
    (roughHarmonicCorrection M g).IsMultiplicative :=
  (squarefreePrimeWeight_isMultiplicative _).mul (squarefreePrimeWeight_isMultiplicative _)

theorem roughHarmonicCorrection_prime (M : ℕ) (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    roughHarmonicCorrection M g p =
      if p ∣ M then 0 else 1 / g p - 1 / (p : ℝ) := by
  rw [roughHarmonicCorrection, roughSieveWeight, squarefreePrimeWeight_mul_prime _ _ hp]
  by_cases hpM : p ∣ M <;> simp [hpM, sub_eq_add_neg]

theorem roughHarmonicCorrection_prime_sq (M : ℕ) (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    roughHarmonicCorrection M g (p ^ 2) =
      if p ∣ M then 0 else -(1 / ((p : ℝ) * g p)) := by
  rw [roughHarmonicCorrection, roughSieveWeight, squarefreePrimeWeight_mul_prime_sq _ _ hp]
  by_cases hpM : p ∣ M <;> simp [hpM, div_eq_mul_inv, mul_comm]

theorem roughHarmonicCorrection_prime_pow_ge_three (M : ℕ) (g : ℕ → ℝ)
    {p j : ℕ} (hp : p.Prime) (hj : 3 ≤ j) :
    roughHarmonicCorrection M g (p ^ j) = 0 :=
  squarefreePrimeWeight_mul_prime_pow_ge_three _ _ hp hj

end

end Erdos4b.FGKMT
