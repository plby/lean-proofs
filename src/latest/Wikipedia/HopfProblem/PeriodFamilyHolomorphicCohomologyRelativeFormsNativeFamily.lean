import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsNativePullbackForms

/-!
# Actual form pullback along the original period-family quotient

The total space carries literally `P.totalChartedSpace`. Its covering
space retains the inherited open-product charts. The pulled-back form
uses the genuine real manifold derivative of the original holomorphic
quotient map.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local instance nativeCoverProductChartedSpace : ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

local instance nativeCoverRealManifold : IsManifold 𝓘(ℝ, Model) ∞ (U × ComplexPlane₂) := by
  change IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ∞ (U × ComplexPlane₂)
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ComplexPlane₂)) U ComplexPlane₂

local instance nativeChartedSpace : ChartedSpace Model P.TotalSpace := P.totalChartedSpace

local instance nativeComplexManifold : IsManifold 𝓘(ℂ, Model) ω P.TotalSpace :=
  P.totalSpace_isManifold

local instance nativeRealManifold : IsManifold 𝓘(ℝ, Model) ∞ P.TotalSpace :=
  Geometry.totalSpace_realManifold P

/-- The genuine native antiholomorphic form pulled back along the
original holomorphic quotient map, in the unchanged covering atlas. -/
def quotientPullback (a : Forms.FormSection Model P.TotalSpace ⊤) :
    Forms.FormSection Model (U × ComplexPlane₂) ⊤ :=
  formPullback Model Model (U × ComplexPlane₂) P.TotalSpace P.quotientMap
    (P.quotientMap_holomorphic.of_le (show ∞ ≤ ω by simp)) a

/-- Evaluation is literal cotangent pullback on original tangent vectors. -/
theorem quotientPullback_apply (a : Forms.FormSection Model P.TotalSpace ⊤)
    (q : U × ComplexPlane₂) (v : Model) :
    Forms.covectorAsModel Model (U × ComplexPlane₂)
        (quotientPullback P a ⟨q, by trivial⟩) v =
      Forms.covectorAsModel Model P.TotalSpace
        (a (toTop P.quotientMap q))
        ((show Model →L[ℝ] Model from
          mfderiv 𝓘(ℝ, Model) 𝓘(ℝ, Model) P.quotientMap q) v) := rfl

/-- The actual native pullback is smooth as a section of the unchanged
covering cotangent Hom bundle. -/
theorem quotientPullback_smooth (a : Forms.FormSection Model P.TotalSpace ⊤) :
    ContMDiff 𝓘(ℝ, Model) (𝓘(ℝ, Model).prod 𝓘(ℝ, Model →L[ℝ] ℂ)) ∞
      (Forms.sectionMap Model (U × ComplexPlane₂) (quotientPullback P a).val) :=
  Forms.FormSection.smooth Model (U × ComplexPlane₂) (quotientPullback P a)

/-- Each covering value is a genuine antiholomorphic covector on the
original three-dimensional complex model. -/
def quotientCovector (a : Forms.FormSection Model P.TotalSpace ⊤)
    (q : U × ComplexPlane₂) : AntiCovector Model :=
  ⟨Forms.covectorAsModel Model (U × ComplexPlane₂)
      (quotientPullback P a ⟨q, by trivial⟩),
    Forms.FormSection.anti Model (U × ComplexPlane₂)
      (quotientPullback P a) ⟨q, by trivial⟩⟩

/-- The actual covector, not a postulated coefficient tuple, evaluates
by the original native quotient derivative. -/
theorem quotientCovector_apply (a : Forms.FormSection Model P.TotalSpace ⊤)
    (q : U × ComplexPlane₂) (v : Model) :
    (quotientCovector P a q).val v =
      Forms.covectorAsModel Model P.TotalSpace
        (a (toTop P.quotientMap q))
        ((show Model →L[ℝ] Model from
          mfderiv 𝓘(ℝ, Model) 𝓘(ℝ, Model) P.quotientMap q) v) := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
