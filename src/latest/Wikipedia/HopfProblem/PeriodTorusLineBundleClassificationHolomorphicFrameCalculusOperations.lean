import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Product and chain rules for the actual native-coordinate ∂̄ operator

Every rule is derived from the ordinary real Fréchet derivative and the
complex-linear projection defining the antiholomorphic coordinate part.
-/

noncomputable section

open Complex
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

open PeriodTorusLineBundleClassification

/-- The native-coordinate product rule. -/
theorem dbarCoordinate_mul {f g : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    dbarCoordinate (fun x => f x * g x) i z =
      f z * dbarCoordinate g i z + g z * dbarCoordinate f i z := by
  have hfg : DifferentiableAt ℝ (fun x => f x * g x) z := hf.mul hg
  rw [dbarCoordinate_eq_linear hfg, fderiv_fun_mul hf hg, map_add,
    dbarCoordinateLinear_complex_smul, dbarCoordinateLinear_complex_smul,
    ← dbarCoordinate_eq_linear hf, ← dbarCoordinate_eq_linear hg]

/-- Negation commutes with the actual coordinate derivative. -/
theorem dbarCoordinate_neg {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (i : Fin 2) :
    dbarCoordinate (fun x => -f x) i z = -dbarCoordinate f i z := by
  have hn : DifferentiableAt ℝ (fun x => -f x) z := hf.neg
  have hd : HasFDerivAt (fun x => -f x) (-fderiv ℝ f z) z := hf.hasFDerivAt.neg
  rw [dbarCoordinate_eq_linear hn, hd.fderiv, map_neg,
    ← dbarCoordinate_eq_linear hf]

/-- The exponential chain rule, with a genuinely real-differentiable
inner function; no holomorphicity of that function is required. -/
theorem dbarCoordinate_cexp {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (i : Fin 2) :
    dbarCoordinate (fun x => Complex.exp (f x)) i z =
      Complex.exp (f z) * dbarCoordinate f i z := by
  rw [dbarCoordinate_eq_linear hf.cexp, hf.hasFDerivAt.cexp.fderiv,
    dbarCoordinateLinear_complex_smul, ← dbarCoordinate_eq_linear hf]

/-- The reciprocal chain rule at a point where the denominator is nonzero. -/
theorem dbarCoordinate_inv {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (hne : f z ≠ 0) (i : Fin 2) :
    dbarCoordinate (fun x => (f x)⁻¹) i z = -dbarCoordinate f i z / (f z) ^ 2 := by
  have hd : HasFDerivAt (fun x => (f x)⁻¹)
      (-(f z ^ 2)⁻¹ • fderiv ℝ f z) z :=
    (hasDerivAt_inv hne).comp_hasFDerivAt z hf.hasFDerivAt
  rw [dbarCoordinate_eq_linear hd.differentiableAt, hd.fderiv,
    dbarCoordinateLinear_complex_smul, ← dbarCoordinate_eq_linear hf]
  ring

/-- The quotient rule for actual native-coordinate derivatives. -/
theorem dbarCoordinate_div {f g : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hne : g z ≠ 0) (i : Fin 2) :
    dbarCoordinate (fun x => f x / g x) i z =
      (dbarCoordinate f i z * g z - f z * dbarCoordinate g i z) / (g z) ^ 2 := by
  have hgi : DifferentiableAt ℝ (fun x => (g x)⁻¹) z :=
    ((hasDerivAt_inv hne).comp_hasFDerivAt z hg.hasFDerivAt).differentiableAt
  have he : (fun x => f x / g x) = (fun x => f x * (g x)⁻¹) :=
    funext (fun x => div_eq_mul_inv (f x) (g x))
  rw [he, dbarCoordinate_mul hf hgi, dbarCoordinate_inv hg hne]
  field_simp
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame
