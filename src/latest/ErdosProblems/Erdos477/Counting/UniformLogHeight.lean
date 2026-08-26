/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform logarithmic height control for the interpolating curve equation.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.UniformEquation

namespace Erdos477.Counting

theorem exists_uniform_log_derivative_bound (D : ℕ) : ∃ L : ℝ, 0 < L ∧
    ∀ B : ℝ, 1 ≤ B → ∀ Q : MvPolynomial (Fin 2) ℤ, Q.totalDegree ≤ D →
    (∀ e, |((Q.coeff e : ℤ) : ℝ)| ≤ planeCoefficientBound D B) →
    ∀ i : Fin 2,
      Real.log (coefficientSum (MvPolynomial.pderiv i Q) + 1 : ℕ) +
        Q.totalDegree * Real.log B + 1 ≤ L * (Real.log B + 1) := by
  let M := (D + 1) ^ 2
  let N := D * M
  let K : ℝ := ((D + 1 : ℝ) ^ 2 * D + 1) * ((D + 1 : ℝ) ^ 2) ^ M
  have hK : 0 < K := by dsimp only [K]; positivity
  let L : ℝ := |Real.log K| + N + D + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro B hB Q hD hcoeff i
  have hB0 : 0 < B := by linarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hH1 := one_le_planeCoefficientBound D B hB
  have hsum := coefficientSum_pderiv_le Q D hD (planeCoefficientBound D B)
    (le_trans zero_le_one hH1) hcoeff i
  have hH : planeCoefficientBound D B = ((D + 1 : ℝ) ^ 2) ^ M * B ^ N := by
    simp only [planeCoefficientBound, M, N, mul_pow, pow_mul]
  have hsum' : ((coefficientSum (MvPolynomial.pderiv i Q) + 1 : ℕ) : ℝ) ≤ K * B ^ N := by
    push_cast
    calc
      _ ≤ ((D + 1 : ℝ) ^ 2 * D) * planeCoefficientBound D B +
          planeCoefficientBound D B := add_le_add hsum hH1
      _ = K * B ^ N := by rw [hH]; dsimp only [K]; ring
  have hlogsum := Real.log_le_log (by positivity :
    (0 : ℝ) < (coefficientSum (MvPolynomial.pderiv i Q) + 1 : ℕ)) hsum'
  rw [Real.log_mul hK.ne' (pow_ne_zero _ hB0.ne'), Real.log_pow] at hlogsum
  have hdegreeR : (Q.totalDegree : ℝ) ≤ D := by exact_mod_cast hD
  have hdegree := mul_le_mul_of_nonneg_right hdegreeR hlog
  have hlogK : Real.log K ≤ |Real.log K| := le_abs_self _
  have hproduct : 0 ≤ (|Real.log K| + 1) * Real.log B := by positivity
  dsimp only [L]
  nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N,
    show (0 : ℝ) ≤ D from Nat.cast_nonneg D]

theorem ceil_height_le_log (C L : ℝ) (hC : 0 ≤ C)
    (B W : ℝ) (hB : 1 ≤ B) (hW : 0 ≤ W) (hbound : W ≤ L * (Real.log B + 1)) :
    ((⌈C * W⌉₊ + 1 : ℕ) : ℝ) ≤ (C * L + 2) * (Real.log B + 1) := by
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hC hW)).le
  have hlog := Real.log_nonneg hB
  have hmul := mul_le_mul_of_nonneg_left hbound hC
  push_cast
  nlinarith

#print axioms exists_uniform_log_derivative_bound
-- 'Erdos477.Counting.exists_uniform_log_derivative_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
