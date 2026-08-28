import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticShearLinear
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# The genuine shear derivative over an arbitrary complex base

The base retains its given one-dimensional complex charts. Translating the
fibre by a base-dependent vector keeps that same base point, so the actual
manifold derivative is the shear formed from the native base derivative.
The proof uses the manifold chain rule and the original product atlas.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates.EllipticShear

variable {B : Type*}

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual gauge translation over the unchanged native base. -/
def gaugeTranslationOn (σ : B → ComplexPlane₂) (x : B × ComplexPlane₂) : B × ComplexPlane₂ :=
  (x.1, x.2 + σ x.1)

@[simp] theorem gaugeTranslationOn_apply (σ : B → ComplexPlane₂) (x : B × ComplexPlane₂) :
    gaugeTranslationOn σ x = (x.1, x.2 + σ x.1) := rfl

variable [TopologicalSpace B] [ChartedSpace ℂ B]

local instance gaugeProductChartedSpace : ChartedSpace (ℂ × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

/-- An analytic local gauge function gives an analytic gauge translation
in the original product charts, without flattening the base. -/
theorem contMDiffAt_gaugeTranslationOn {σ : B → ComplexPlane₂} {b : B}
    (hσ : ContMDiffAt I₁ I₂ ω σ b) (ζ : ComplexPlane₂) :
    ContMDiffAt IF IF ω (gaugeTranslationOn σ) (b, ζ) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiffAt_fst.prodMk
    (contMDiffAt_snd.add (hσ.comp (b, ζ) contMDiffAt_fst))

theorem mdifferentiableAt_gaugeTranslationOn {σ : B → ComplexPlane₂} {b : B}
    (hσ : MDifferentiableAt I₁ I₂ σ b) (ζ : ComplexPlane₂) :
    MDifferentiableAt IF IF (gaugeTranslationOn σ) (b, ζ) := by
  rw [modelWithCornersSelf_prod]
  exact mdifferentiableAt_fst.prodMk
    (mdifferentiableAt_snd.add (hσ.comp (b, ζ) mdifferentiableAt_fst))

/-- The actual manifold derivative in the two native product charts.
Its scalar-to-vector block is recovered by evaluation at the unit tangent
vector of the given one-dimensional base chart. -/
theorem mfderiv_gaugeTranslationOn {σ : B → ComplexPlane₂} {b : B}
    (hσ : MDifferentiableAt I₁ I₂ σ b) (ζ : ComplexPlane₂) :
    mfderiv IF IF (gaugeTranslationOn σ) (b, ζ) =
      shear (mfderiv I₁ I₂ σ b (1 : ℂ)) := by
  let L : ℂ →L[ℂ] ComplexPlane₂ := mfderiv I₁ I₂ σ b
  change mfderiv IF IF (gaugeTranslationOn σ) (b, ζ) = shear (L 1)
  rw [modelWithCornersSelf_prod]
  have hf : HasMFDerivAt ((I₁).prod I₂) I₁
      (fun x : B × ComplexPlane₂ => x.1) (b, ζ)
      (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂) := hasMFDerivAt_fst (b, ζ)
  have hv : HasMFDerivAt ((I₁).prod I₂) I₂
      (fun x : B × ComplexPlane₂ => x.2) (b, ζ)
      (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) := hasMFDerivAt_snd (b, ζ)
  have hσ' : HasMFDerivAt I₁ I₂ σ b L := hσ.hasMFDerivAt
  have hs := hσ'.comp (b, ζ) hf
  have hd := hf.prodMk (hv.add hs)
  have hc : (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).prod
      ((ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) +
        L.comp (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂)) = shear (L 1) := by
    apply ContinuousLinearMap.ext
    intro w
    change (w.1, w.2 + L w.1) = (w.1, w.2 + w.1 • L 1)
    apply Prod.ext
    · rfl
    · apply congrArg (fun v : ComplexPlane₂ => w.2 + v)
      simpa only [smul_eq_mul, mul_one] using L.map_smul w.1 (1 : ℂ)
  exact hd.mfderiv.trans hc

theorem mfderiv_gaugeTranslationOn_apply {σ : B → ComplexPlane₂} {b : B}
    (hσ : MDifferentiableAt I₁ I₂ σ b) (ζ : ComplexPlane₂) (w : ℂ × ComplexPlane₂) :
    let L : ℂ →L[ℂ] ComplexPlane₂ := mfderiv I₁ I₂ σ b
    mfderiv IF IF (gaugeTranslationOn σ) (b, ζ) w =
      (w.1, w.2 + w.1 • L 1) :=
  congrArg (fun A : (ℂ × ComplexPlane₂) →L[ℂ] (ℂ × ComplexPlane₂) => A w)
    (mfderiv_gaugeTranslationOn hσ ζ)

end Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates.EllipticShear
