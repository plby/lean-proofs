import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsNativeFamily
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsFrame

/-!
# Actual frame coefficients of the native quotient pullback

The input is a genuine section of the original quotient's cotangent
bundle. The coefficients below are extracted from its actual pullback by
the proved inverse frame. Their reconstruction is equality of the
original covectors, not a representation assumption.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold ComplexConjugate

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local instance frameCoverProductChartedSpace : ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

local instance frameNativeChartedSpace : ChartedSpace Model P.TotalSpace := P.totalChartedSpace

local instance frameNativeComplexManifold : IsManifold 𝓘(ℂ, Model) ω P.TotalSpace :=
  P.totalSpace_isManifold

local instance frameNativeRealManifold : IsManifold 𝓘(ℝ, Model) ∞ P.TotalSpace :=
  Geometry.totalSpace_realManifold P

/-- The three actual coefficients of the genuine native pullback in the
full inverse-period antiholomorphic frame. -/
def quotientCoefficients (a : Forms.FormSection Model P.TotalSpace ⊤)
    (q : U × ComplexPlane₂) : Model :=
  (frameEquiv P q.1 q.2).symm (quotientCovector P a q)

/-- The frame extractor is the explicit triangular solve already proved
from the literal inverse-period coordinate derivatives. -/
theorem quotientCoefficients_eq_frameCoefficients
    (a : Forms.FormSection Model P.TotalSpace ⊤) (q : U × ComplexPlane₂) :
    quotientCoefficients P a q =
      frameCoefficients P q.1 q.2 (quotientCovector P a q) :=
  frameEquiv_symm_apply P q.1 q.2 (quotientCovector P a q)

/-- The extracted coefficients reconstruct the actual pulled-back native
covector on the original model. -/
theorem frameLinear_quotientCoefficients
    (a : Forms.FormSection Model P.TotalSpace ⊤) (q : U × ComplexPlane₂) :
    frameLinear P ((q.1 : ℂ), q.2) (quotientCoefficients P a q) =
      quotientCovector P a q :=
  (frameEquiv P q.1 q.2).apply_symm_apply (quotientCovector P a q)

/-- Reconstruction evaluates to the literal original cotangent pullback,
with the actual full antiholomorphic coordinate differentials. -/
theorem quotientPullback_frame_apply
    (a : Forms.FormSection Model P.TotalSpace ⊤) (q : U × ComplexPlane₂) (v : Model) :
    Forms.covectorAsModel Model P.TotalSpace
        (a (toTop P.quotientMap q))
        ((show Model →L[ℝ] Model from
          mfderiv 𝓘(ℝ, Model) 𝓘(ℝ, Model) P.quotientMap q) v) =
      (quotientCoefficients P a q).1 * conj v.1 +
        (quotientCoefficients P a q).2 0 *
          dbar (coordinate P 0) ((q.1 : ℂ), q.2) v +
        (quotientCoefficients P a q).2 1 *
          dbar (coordinate P 1) ((q.1 : ℂ), q.2) v := by
  have h := congrArg (fun L : AntiCovector Model => L.val v)
    (frameLinear_quotientCoefficients P a q)
  exact h.symm

/-- The proved pointwise frame makes the actual coefficient extraction
unique, without imposing a spanning axiom on native form sections. -/
theorem quotientCoefficients_unique
    (a : Forms.FormSection Model P.TotalSpace ⊤) (q : U × ComplexPlane₂) (c : Model)
    (hc : frameLinear P ((q.1 : ℂ), q.2) c = quotientCovector P a q) :
    c = quotientCoefficients P a q :=
  frameLinear_injective P q.1 q.2 (hc.trans (frameLinear_quotientCoefficients P a q).symm)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
