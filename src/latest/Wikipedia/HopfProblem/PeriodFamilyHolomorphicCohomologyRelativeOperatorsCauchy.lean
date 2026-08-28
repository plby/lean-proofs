import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsFourier
import Mathlib.Analysis.Complex.Conformal

/-!
# The actual base Cauchy--Riemann criterion

Vanishing of the scalar operator `d0` is equivalent to complex
differentiability in the original base variable. The same criterion holds
for the genuine Haar coefficients. Real differentiability is supplied by
the smooth family and its proved parameter differentiation theorem.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators

open FourierParameter

private theorem half_dbar_eq_zero_iff (a b : ℂ) :
    (a + Complex.I * b) / 2 = 0 ↔ b = Complex.I * a := by
  constructor
  · intro h
    have hs : a + Complex.I * b = 0 :=
      (div_eq_zero_iff.mp h).resolve_right (by norm_num)
    have hi := congrArg (fun z : ℂ => Complex.I * z) hs
    have he : Complex.I * a - b = 0 := by
      simpa only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
        mul_zero, sub_eq_add_neg] using hi
    exact (sub_eq_zero.mp he).symm
  · intro h
    rw [h]
    simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul, add_neg_cancel, zero_div]

/-- The scalar antiholomorphic derivative vanishes exactly at complex-differentiable points. -/
theorem baseDbar_eq_zero_iff_differentiableAt {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2 = 0 ↔
      DifferentiableAt ℂ g z := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  simpa only [hg, true_and, smul_eq_mul] using
    half_dbar_eq_zero_iff (fderiv ℝ g z 1) (fderiv ℝ g z Complex.I)

variable {U : Opens ℂ} {d : Type*} [Fintype d]

/-- At each actual torus point, `d0` detects complex differentiability in the base. -/
theorem d0_eq_zero_iff_differentiableAt (f : SmoothFamily U d) (b : U)
    (t : UnitAddTorus d) :
    d0 f (b, t) = 0 ↔
      DifferentiableAt ℂ (fun z : ℂ => ambientValue f (z, t)) (b : ℂ) := by
  rw [d0_apply, SmoothFamily.baseDerivative_apply, SmoothFamily.baseDerivative_apply]
  simpa only [(f.ambientValue_hasFDerivAt b t).fderiv] using
    baseDbar_eq_zero_iff_differentiableAt (f.ambientValue_hasFDerivAt b t).differentiableAt

/-- The actual coefficient of `d0 f` detects complex differentiability of that Haar coefficient. -/
theorem coefficientValue_d0_eq_zero_iff (f : SmoothFamily U d) (k : d → ℤ) (b : U) :
    (d0 f).coefficientValue k (b : ℂ) = 0 ↔
      DifferentiableAt ℂ (f.coefficientValue k) (b : ℂ) := by
  rw [coefficientValue_d0]
  exact baseDbar_eq_zero_iff_differentiableAt (f.coefficientValue_hasFDerivAt k b).differentiableAt

/-- Vanishing on the original open base gives genuine complex differentiability there. -/
theorem coefficientValue_differentiableOn_of_d0_zero (f : SmoothFamily U d) (k : d → ℤ)
    (h : ∀ b : U, (d0 f).coefficientValue k (b : ℂ) = 0) :
    DifferentiableOn ℂ (f.coefficientValue k) U := by
  intro z hz
  exact ((coefficientValue_d0_eq_zero_iff f k ⟨z, hz⟩).mp (h ⟨z, hz⟩)).differentiableWithinAt

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators
