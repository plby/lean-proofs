import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCauchyIntegral

/-!
# Calculus rules for the actual antiholomorphic differential

The product and subtraction rules and the parameter-integral bridges below
are equalities of the original real Fréchet derivatives.  In particular, the
Cauchy–Green parameter operator is the actual `(0,1)` differential evaluated
on a parameter vector.
-/

noncomputable section

open Complex
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

@[simp] theorem dbar_const (c : ℂ) (q : E) : dbar (fun _ : E => c) q = 0 := by
  rw [dbar, fderiv_const_apply, antiPart_zero]

theorem dbar_sub {f g : E → ℂ} {q : E}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbar (f - g) q = dbar f q - dbar g q := by
  rw [dbar, fderiv_sub hf hg]
  exact map_sub antiPartLinear _ _

theorem dbar_mul {f g : E → ℂ} {q : E}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbar (fun x => f x * g x) q = f q • dbar g q + g q • dbar f q := by
  rw [dbar, fderiv_fun_mul hf hg, antiPart_add,
    antiPart_complex_smul, antiPart_complex_smul]
  rfl

/-- A fixed directional coefficient of the actual differential is smooth. -/
theorem contDiff_dbar_apply {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun q => dbar f q v) :=
  (contDiff_dbar hf).clm_apply contDiff_const

/-- The same smoothness statement is local at the original point. -/
theorem contDiffAt_dbar {f : E → ℂ} {q : E} (hf : ContDiffAt ℝ ∞ f q) :
    ContDiffAt ℝ ∞ (dbar f) q :=
  antiPartLinear.contDiff.contDiffAt.comp q (hf.fderiv_right (by simp))

theorem contDiffAt_dbar_apply {f : E → ℂ} {q : E}
    (hf : ContDiffAt ℝ ∞ f q) (v : E) :
    ContDiffAt ℝ ∞ (fun x => dbar f x v) q :=
  (contDiffAt_dbar hf).clm_apply contDiffAt_const

namespace Cauchy

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P]

/-- The parameter operator is literally evaluation of the actual
antiholomorphic differential on the corresponding joint vector. -/
theorem parameterDbar_eq_dbar (v : P) (f : P × ℂ → ℂ) (q : P × ℂ) :
    parameterDbar v f q = dbar f q (v, 0) := by
  simp only [parameterDbar_eq_formula, dbar_apply, Prod.smul_mk, smul_zero]

/-- The slice derivative is the same actual differential evaluated in the
last complex coordinate, at every real-differentiable point. -/
theorem lastDbar_eq_dbar {f : P × ℂ → ℂ} {q : P × ℂ}
    (hf : DifferentiableAt ℝ f q) : lastDbar f q = dbar f q (0, 1) := by
  rw [lastDbar_eq_formula hf, dbar_apply]
  simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]

end Cauchy

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree
