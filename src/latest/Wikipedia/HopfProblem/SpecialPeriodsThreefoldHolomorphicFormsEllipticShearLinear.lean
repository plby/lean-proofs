import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The actual linear shear of a holomorphic fibre translation

The map on tangent vectors is the genuine continuous complex-linear shear
`(u, v) ↦ (u, v + u • d)`. The ordinary chain rule identifies it with the
Fréchet derivative of `(z, ζ) ↦ (z, ζ + σ z)` whenever the vector-valued
function `σ` has derivative `d`. No coefficient transformation is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates.EllipticShear

local notation "V" => ℂ × ComplexPlane₂

/-- The actual derivative shear on the base-first period-coordinate model. -/
def shear (d : ComplexPlane₂) : V →L[ℂ] V :=
  (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).prod
    ((ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) +
      (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).smulRight d)

@[simp] theorem shear_apply (d : ComplexPlane₂) (w : V) :
    shear d w = (w.1, w.2 + w.1 • d) := rfl

@[simp] theorem shear_vertical (d v : ComplexPlane₂) :
    shear d (0, v) = (0, v) := by
  simp only [shear_apply, zero_smul, add_zero]

@[simp] theorem shear_base (d : ComplexPlane₂) :
    shear d (1, 0) = (1, d) := by
  simp only [shear_apply, one_smul, zero_add]

@[simp] theorem shear_zero : shear 0 = ContinuousLinearMap.id ℂ V := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [shear_apply, smul_zero, add_zero, ContinuousLinearMap.id_apply]

theorem shear_comp (d e : ComplexPlane₂) : (shear e).comp (shear d) = shear (d + e) := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, shear_apply, smul_add, add_assoc]

theorem shear_neg_cancel (d : ComplexPlane₂) (w : V) : shear (-d) (shear d w) = w := by
  have he := congrArg (fun L : V →L[ℂ] V => L w) (shear_comp d (-d))
  simpa only [ContinuousLinearMap.comp_apply, add_neg_cancel, shear_zero,
    ContinuousLinearMap.id_apply] using he

/-- The original fibre translation, expressed in its actual vector coordinates. -/
def gaugeTranslation (σ : ℂ → ComplexPlane₂) (w : V) : V :=
  (w.1, w.2 + σ w.1)

@[simp] theorem gaugeTranslation_apply (σ : ℂ → ComplexPlane₂) (w : V) :
    gaugeTranslation σ w = (w.1, w.2 + σ w.1) := rfl

theorem gaugeTranslation_neg_cancel (σ : ℂ → ComplexPlane₂) (w : V) :
    gaugeTranslation (fun z => -σ z) (gaugeTranslation σ w) = w := by
  simp only [gaugeTranslation_apply, add_neg_cancel_right]

/-- The ordinary Fréchet derivative of the actual gauge map is exactly
the displayed continuous linear shear. -/
theorem hasFDerivAt_gaugeTranslation {σ : ℂ → ComplexPlane₂} {z : ℂ}
    {d : ComplexPlane₂} (hσ : HasDerivAt σ d z) (ζ : ComplexPlane₂) :
    HasFDerivAt (gaugeTranslation σ) (shear d) (z, ζ) := by
  have hf : HasFDerivAt (fun w : V => w.1)
      (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂) (z, ζ) := hasFDerivAt_fst
  have hv : HasFDerivAt (fun w : V => w.2)
      (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) (z, ζ) := hasFDerivAt_snd
  have hs := hσ.hasFDerivAt.comp (z, ζ) hf
  exact hf.prodMk (hv.add hs)

/-- In particular the actual derivative is the shear determined by the
genuine vector-valued derivative of `σ`. -/
theorem fderiv_gaugeTranslation {σ : ℂ → ComplexPlane₂} {z : ℂ}
    (hσ : DifferentiableAt ℂ σ z) (ζ : ComplexPlane₂) :
    fderiv ℂ (gaugeTranslation σ) (z, ζ) = shear (deriv σ z) :=
  (hasFDerivAt_gaugeTranslation hσ.hasDerivAt ζ).fderiv

theorem hasFDerivAt_gaugeTranslation_fun {σ : ℂ → ComplexPlane₂} {z : ℂ}
    {d : ComplexPlane₂} (hσ : HasDerivAt σ d z) (ζ : ComplexPlane₂) :
    HasFDerivAt (fun w : V => (w.1, w.2 + σ w.1)) (shear d) (z, ζ) :=
  hasFDerivAt_gaugeTranslation hσ ζ

end Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates.EllipticShear
