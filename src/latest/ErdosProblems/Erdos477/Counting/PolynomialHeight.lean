/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Coefficient and evaluation height bounds for plane polynomials.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

noncomputable def coefficientSum (P : MvPolynomial (Fin 2) ℤ) : ℕ :=
  ∑ m ∈ P.support, (P.coeff m).natAbs

lemma natAbs_cast_eq_abs (a : ℤ) : (a.natAbs : ℝ) = |(a : ℝ)| := by
  simpa only [Int.cast_natCast, Int.cast_abs] using
    congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs a)

theorem abs_eval_le_coefficientSum_mul_pow (P : MvPolynomial (Fin 2) ℤ)
    (D : ℕ) (hD : P.totalDegree ≤ D) (z : Fin 2 → ℤ)
    (B : ℝ) (hB : 1 ≤ B) (hz : ∀ k, |(z k : ℝ)| ≤ B) :
    |(MvPolynomial.eval z P : ℝ)| ≤ (coefficientSum P : ℝ) * B ^ D := by
  have heval : (MvPolynomial.eval z P : ℝ) =
      ∑ m ∈ P.support, ((P.coeff m : ℤ) : ℝ) * ((z 0 : ℝ) ^ m 0 * (z 1 : ℝ) ^ m 1) := by
    rw [MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two]
    push_cast
    rfl
  rw [heval]
  calc
    _ ≤ ∑ m ∈ P.support, |((P.coeff m : ℤ) : ℝ) * ((z 0 : ℝ) ^ m 0 * (z 1 : ℝ) ^ m 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ P.support, ((P.coeff m).natAbs : ℝ) * B ^ D := by
      apply Finset.sum_le_sum
      intro m hm
      have hdegree : m 0 + m 1 ≤ D := by
        have h := (MvPolynomial.le_totalDegree hm).trans hD
        rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
        exact h
      rw [abs_mul, abs_mul, abs_pow, abs_pow, ← natAbs_cast_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        _ ≤ B ^ m 0 * B ^ m 1 := by gcongr <;> exact hz _
        _ = B ^ (m 0 + m 1) := (pow_add ..).symm
        _ ≤ B ^ D := pow_le_pow_right₀ hB hdegree
    _ = _ := by simp only [← Finset.sum_mul, coefficientSum, Nat.cast_sum]

theorem log_abs_eval_le_coefficientSum (P : MvPolynomial (Fin 2) ℤ)
    (D : ℕ) (hD : P.totalDegree ≤ D) (z : Fin 2 → ℤ) (hzero : MvPolynomial.eval z P ≠ 0)
    (B : ℝ) (hB : 1 ≤ B) (hz : ∀ k, |(z k : ℝ)| ≤ B) :
    Real.log |(MvPolynomial.eval z P : ℝ)| ≤
      Real.log (coefficientSum P + 1 : ℕ) + D * Real.log B := by
  have hB0 : 0 < B := by linarith
  have hsum : (coefficientSum P : ℝ) ≤ (coefficientSum P + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ (coefficientSum P)
  have hbound := (abs_eval_le_coefficientSum_mul_pow P D hD z B hB hz).trans
    (mul_le_mul_of_nonneg_right hsum (pow_nonneg hB0.le D))
  have hpos : 0 < |(MvPolynomial.eval z P : ℝ)| := abs_pos.mpr (by exact_mod_cast hzero)
  have h := Real.log_le_log hpos hbound
  rwa [Real.log_mul (by positivity) (pow_ne_zero _ hB0.ne'), Real.log_pow] at h

#print axioms log_abs_eval_le_coefficientSum
-- 'Erdos477.Counting.log_abs_eval_le_coefficientSum' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
