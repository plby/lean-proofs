import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsRegularity
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Real smoothness of the actual full antiholomorphic frame

The original frame is regarded as a continuous real-linear map into the
subspace of genuine antiholomorphic covectors. Its smoothness follows from
the proved smoothness of its values on fixed vectors, by finite dimension.
No new chart or assumed regularity of an inverse is introduced.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

/-- The actual antiholomorphic-part projection, with its proved range. -/
def antiCovectorProjection : (Model →L[ℝ] ℂ) →L[ℝ] AntiCovector Model :=
  antiPartLinear.codRestrict (antiCovectors.restrictScalars ℝ) antiPart_mem

/-- The projection fixes every genuine antiholomorphic covector. -/
@[simp] theorem antiCovectorProjection_val (L : AntiCovector Model) :
    antiCovectorProjection L.val = L := by
  apply Subtype.ext
  exact antiPart_eq_self L.property

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local instance nativeCoverProductChartedSpace : ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

/-- The original complex-linear frame, viewed as a continuous real-linear map. -/
def frameRealLinear (q : Model) : Model →L[ℝ] AntiCovector Model :=
  ((frameLinear P q).restrictScalars ℝ).toContinuousLinearMap

@[simp] theorem frameRealLinear_apply (q c : Model) :
    frameRealLinear P q c = frameLinear P q c := rfl

/-- The genuine pointwise frame equivalence in the original real normed models. -/
def frameRealEquiv (b : U) (z : ComplexPlane₂) :
    Model ≃L[ℝ] AntiCovector Model :=
  ((frameEquiv P b z).restrictScalars ℝ).toContinuousLinearEquiv

@[simp] theorem frameRealEquiv_toContinuousLinearMap (b : U) (z : ComplexPlane₂) :
    (frameRealEquiv P b z).toContinuousLinearMap = frameRealLinear P ((b : ℂ), z) := by
  apply ContinuousLinearMap.ext
  intro c
  rfl

@[simp] theorem frameRealEquiv_symm_apply (b : U) (z : ComplexPlane₂)
    (L : AntiCovector Model) :
    (frameRealEquiv P b z).symm L = (frameEquiv P b z).symm L := rfl

/-- Smoothness of the actual operator-valued frame on the full original open domain. -/
theorem frameRealLinear_contDiffOn :
    ContDiffOn ℝ ∞ (frameRealLinear P) (Smooth.baseProductDomain U ComplexPlane₂) := by
  apply contDiffOn_clm_apply.mpr
  intro c
  have h := antiCovectorProjection.contDiff.comp_contDiffOn (frameLinear_contDiffOn P c)
  simpa only [Function.comp_def, antiCovectorProjection_val, frameRealLinear_apply] using h

/-- The full operator-valued frame is smooth in the inherited open-base product chart. -/
theorem frameRealLinear_contMDiff :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model →L[ℝ] AntiCovector Model) ∞
      (fun q : U × ComplexPlane₂ => frameRealLinear P ((q.1 : ℂ), q.2)) :=
  Smooth.contMDiff_productOpen_of_contDiffOn (frameRealLinear_contDiffOn P)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
