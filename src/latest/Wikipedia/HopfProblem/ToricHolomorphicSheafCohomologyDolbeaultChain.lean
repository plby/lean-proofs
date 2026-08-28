import Wikipedia.HopfProblem.HolomorphicCousinWirtinger
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The actual antiholomorphic chart-transition rule

The antiholomorphic differential transforms by the conjugate of the
complex derivative of the coordinate change. In particular the two
standard sphere coordinates have the literal transition coefficient
`conj (-(z ^ 2)⁻¹)`. This is calculated from the genuine real Fréchet
derivative, not imposed as a convention on function coefficients.
-/

noncomputable section

open Complex ComplexConjugate Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal

open HolomorphicCousin

/-- Evaluation of a real-linear differential in the standard real basis. -/
theorem realLinear_apply (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = (z.re : ℂ) * L 1 + (z.im : ℂ) * L I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  refine (congrArg L hz).trans ?_
  calc
    L (z.re • (1 : ℂ) + z.im • I) = L (z.re • (1 : ℂ)) + L (z.im • I) :=
      L.map_add _ _
    _ = z.re • L 1 + z.im • L I :=
      congrArg₂ (fun a b : ℂ => a + b) (L.map_smul z.re 1) (L.map_smul z.im I)
    _ = (z.re : ℂ) * L 1 + (z.im : ℂ) * L I := by
      rw [Complex.real_smul, Complex.real_smul]

/-- Precomposition by an actual complex-linear differential multiplies
the antiholomorphic component by the conjugate complex coefficient. -/
theorem dbarLinear_comp_complex (L : ℂ →L[ℝ] ℂ) (a : ℂ) :
    dbarLinear (L.comp ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ)) =
      conj a * dbarLinear L := by
  have hconj : conj a = (a.re : ℂ) - (a.im : ℂ) * I := by
    apply Complex.ext <;> simp
  simp only [dbarLinear_apply]
  change (L ((1 : ℂ) * a) + I * L (I * a)) / 2 =
    conj a * ((L 1 + I * L I) / 2)
  rw [one_mul, realLinear_apply L a, realLinear_apply L (I * a), hconj]
  simp only [mul_re, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub, zero_add,
    ofReal_neg]
  ring_nf
  rw [I_sq]
  ring

/-- Genuine holomorphic coordinate changes have the expected actual
antiholomorphic derivative chain rule. -/
theorem dbar_comp_of_hasDerivAt {f c : ℂ → ℂ} {a z : ℂ}
    (hf : DifferentiableAt ℝ f (c z)) (hc : HasDerivAt c a z) :
    dbar (f ∘ c) z = conj a * dbar f (c z) := by
  have hd := (hf.hasFDerivAt.comp z (hc.hasFDerivAt.restrictScalars ℝ)).fderiv
  simpa only [dbar_eq_dbarLinear] using
    (congrArg dbarLinear hd).trans (dbarLinear_comp_complex (fderiv ℝ f (c z)) a)

/-- The actual two sphere charts therefore have this precise derivative
transition on their overlap. -/
theorem dbar_comp_inv {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : DifferentiableAt ℝ f z⁻¹) :
    dbar (fun w => f w⁻¹) z = conj (-(z ^ 2)⁻¹) * dbar f z⁻¹ :=
  dbar_comp_of_hasDerivAt hf (hasDerivAt_inv hz)

/-- Equal actual germs have equal antiholomorphic derivatives. -/
theorem dbar_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  simp only [dbar_eq_dbarLinear]
  exact congrArg dbarLinear h.fderiv_eq

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal
