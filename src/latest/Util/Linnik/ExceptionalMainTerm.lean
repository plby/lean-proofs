import ErdosProblems.Erdos48.EndpointMiddleZero

/-!
# The principal main term after an exceptional zero

The real exceptional kernel cannot cancel the whole principal main term.
The surviving proportion is comparable to the exceptional gap multiplied
by the logarithm of the endpoint.
-/

namespace Linnik

open Complex BoundedGaps.Maynard

theorem one_sub_exp_neg_half_ge_min {y : ℝ} (hy : 0 ≤ y) :
    min 1 y / 4 ≤ 1 - Real.exp (-y / 2) := by
  let v : ℝ := min 1 y
  have hv₀ : 0 ≤ v := le_min (by norm_num) hy
  have hv₁ : v ≤ 1 := min_le_left _ _
  have hvy : v ≤ y := min_le_right _ _
  have hden : 0 < 1 + v / 2 := by linarith
  have hexp : Real.exp (-y / 2) ≤ 1 / (1 + v / 2) := by
    calc
      Real.exp (-y / 2) ≤ Real.exp (-(v / 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / Real.exp (v / 2) := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / (1 + v / 2) := one_div_le_one_div_of_le hden (by linarith [Real.add_one_le_exp (v / 2)])
  have hfrac : 1 / (1 + v / 2) ≤ 1 - v / 4 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hv₀ (sub_nonneg.mpr hv₁)]
  linarith

theorem neg_log_le_twice_gap {beta : ℝ} (hbeta₀ : 1 / 2 ≤ beta) (hbeta₁ : beta ≤ 1) :
    -Real.log beta ≤ 2 * (1 - beta) := by
  have hbeta : 0 < beta := by linarith
  have hinv : beta⁻¹ ≤ 3 - 2 * beta := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hbeta).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2 * beta - 1 by linarith) (sub_nonneg.mpr hbeta₁)]
  linarith [Real.one_sub_inv_le_log_of_pos hbeta]

theorem exceptional_rpow_div_le
    {x beta : ℝ} (hx : 0 < x) (hlog : 4 ≤ Real.log x)
    (hbeta₀ : 1 / 2 ≤ beta) (hbeta₁ : beta ≤ 1) :
    x ^ beta / beta ≤ x * Real.exp (-(1 - beta) * Real.log x / 2) := by
  have hbeta : 0 < beta := by linarith
  have hlogBeta := neg_log_le_twice_gap hbeta₀ hbeta₁
  have heps : 0 ≤ 1 - beta := sub_nonneg.mpr hbeta₁
  calc
    x ^ beta / beta = Real.exp (beta * Real.log x - Real.log beta) := by
      rw [Real.exp_sub, Real.exp_log hbeta, Real.rpow_def_of_pos hx]
      congr 2
      ring
    _ ≤ Real.exp (Real.log x + (-(1 - beta) * Real.log x / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg heps (show 0 ≤ Real.log x - 4 by linarith)]
    _ = x * Real.exp (-(1 - beta) * Real.log x / 2) := by rw [Real.exp_add, Real.exp_log hx]

theorem exceptionalKernel_eq_ofReal
    {x beta : ℝ} (hx : 0 < x) (hbeta : 0 < beta) :
    dirichletExplicitFormulaKernel x (beta : ℂ) = (((x ^ beta - 1) / beta : ℝ) : ℂ) := by
  rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hx (by exact_mod_cast hbeta.ne')]
  rw [← Complex.ofReal_cpow hx.le]
  push_cast
  rfl

theorem norm_exceptionalKernel_eq
    {x beta : ℝ} (hx : 1 ≤ x) (hbeta : 0 < beta) :
    ‖dirichletExplicitFormulaKernel x (beta : ℂ)‖ = (x ^ beta - 1) / beta := by
  rw [exceptionalKernel_eq_ofReal (zero_lt_one.trans_le hx) hbeta, Complex.norm_real,
    Real.norm_of_nonneg]
  exact div_nonneg (sub_nonneg.mpr (Real.one_le_rpow hx hbeta.le)) hbeta.le

/-- A uniform quantitative lower bound for the main term with its one
exceptional-zero kernel subtracted. -/
theorem mainTerm_sub_exceptionalKernel_ge
    {x beta : ℝ} (hx : 1 ≤ x) (hlog : 4 ≤ Real.log x)
    (hbeta₀ : 1 / 2 ≤ beta) (hbeta₁ : beta ≤ 1) :
    x / 4 * min 1 ((1 - beta) * Real.log x) ≤
      x - ‖dirichletExplicitFormulaKernel x (beta : ℂ)‖ := by
  have hbeta : 0 < beta := by linarith
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [norm_exceptionalKernel_eq hx hbeta]
  have hkernel : (x ^ beta - 1) / beta ≤ x ^ beta / beta := by gcongr; linarith
  have hpower := exceptional_rpow_div_le hx₀ hlog hbeta₀ hbeta₁
  have hmin := one_sub_exp_neg_half_ge_min
    (mul_nonneg (sub_nonneg.mpr hbeta₁) (Real.log_nonneg hx))
  have hexp : Real.exp (-((1 - beta) * Real.log x) / 2) =
      Real.exp (-(1 - beta) * Real.log x / 2) := by congr 1; ring
  rw [hexp] at hmin
  have hscaled := mul_le_mul_of_nonneg_left hmin hx₀.le
  nlinarith

end Linnik
