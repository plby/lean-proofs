import ErdosProblems.Erdos906.PointwiseLogTail

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Real

namespace CofiniteDerivatives

noncomputable section

/-- Every bounded-coefficient Fock series has an explicit quadratic exponential majorant. -/
theorem norm_fockFunction_le_sqrt_two_mul_exp_sq
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (z : ℂ) :
    ‖fockFunction ξ z‖ ≤ √2 * Real.exp (‖z‖ ^ 2) := by
  have hderiv := norm_pointwiseDerivativeSeries_le_saddleSeries hξ 0 z
  rw [pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction ξ hξ, iteratedDeriv_zero]
    at hderiv
  refine hderiv.trans ?_
  rw [saddleSeries_eq_sqrt_factorial_mul_normalized]
  simp only [Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, one_mul]
  have hbound :=
    (normalizedSaddleSeries_summable_and_le_cauchySchwarz 0 (norm_nonneg z)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)).2
  calc
    normalizedSaddleSeries 0 ‖z‖ ≤
        √((1 / (1 - (1 / 2 : ℝ))) ^ (0 + 1)) *
          √(Real.exp (‖z‖ ^ 2 / (1 / 2 : ℝ))) := hbound
    _ = √2 * Real.exp (‖z‖ ^ 2) := by
      rw [show (1 / (1 - (1 / 2 : ℝ))) ^ (0 + 1) = 2 by norm_num]
      rw [show ‖z‖ ^ 2 / (1 / 2 : ℝ) = 2 * ‖z‖ ^ 2 by ring]
      rw [show 2 * ‖z‖ ^ 2 = ‖z‖ ^ 2 + ‖z‖ ^ 2 by ring, Real.exp_add,
        Real.sqrt_mul_self (Real.exp_nonneg _)]

end

end CofiniteDerivatives
