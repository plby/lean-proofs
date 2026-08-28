import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsNativeCoverBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBasic

/-!
# Smooth raw covector values of native forms on the original cover

On this particular open-product cover, the genuine native tangent
trivializations are identity maps. Native cotangent coordinates therefore
equal the defining model values, and their smoothness follows from the
actual native form-section smoothness.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

attribute [local instance] coverChartedSpace coverRealManifold

variable {U : Opens ℂ}

/-- In the actual flat cover charts, native cotangent coordinates are
literally the raw model values of the same original covectors. -/
theorem cover_inCoordinates_eq {V : Opens (U × ComplexPlane₂)}
    (a : ∀ x : V, Forms.Covector Model (U × ComplexPlane₂) (x : U × ComplexPlane₂))
    (p : U × ComplexPlane₂) (x : V) :
    Forms.inCoordinates Model (U × ComplexPlane₂) a p x =
      Forms.covectorAsModel Model (U × ComplexPlane₂) (a x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [Forms.inCoordinates_apply]
  exact congrArg (Forms.covectorAsModel Model (U × ComplexPlane₂) (a x))
    (cover_symmL_trivializationAt_apply p (x : U × ComplexPlane₂) v)

/-- The actual model value of a native global form on the original
open-product cover, evaluated on the literal top-open section. -/
def coverCovector (a : Forms.FormSection Model (U × ComplexPlane₂) ⊤)
    (q : U × ComplexPlane₂) : Model →L[ℝ] ℂ :=
  Forms.covectorAsModel Model (U × ComplexPlane₂) (a ⟨q, by trivial⟩)

@[simp] theorem coverCovector_apply
    (a : Forms.FormSection Model (U × ComplexPlane₂) ⊤)
    (q : U × ComplexPlane₂) (v : Model) :
    coverCovector a q v = a ⟨q, by trivial⟩ v := rfl

/-- These values retain the actual anti-linearity of the original native
form section; it is not an extra property assumed of a coordinate family. -/
theorem coverCovector_mem
    (a : Forms.FormSection Model (U × ComplexPlane₂) ⊤) (q : U × ComplexPlane₂) :
    coverCovector a q ∈ antiCovectors :=
  Forms.FormSection.anti Model (U × ComplexPlane₂) a ⟨q, by trivial⟩

/-- The same original covector packaged in its proved antiholomorphic
model subspace, for use in the genuine full frame. -/
def coverAntiCovector (a : Forms.FormSection Model (U × ComplexPlane₂) ⊤)
    (q : U × ComplexPlane₂) : AntiCovector Model :=
  ⟨coverCovector a q, coverCovector_mem a q⟩

@[simp] theorem coverAntiCovector_val
    (a : Forms.FormSection Model (U × ComplexPlane₂) ⊤) (q : U × ComplexPlane₂) :
    (coverAntiCovector a q).val = coverCovector a q := rfl

/-- Genuine native smoothness implies smoothness of the raw model
covectors on this original flat open-product cover. The proof uses the
actual native coordinates and the literal top-open subtype restriction. -/
theorem coverCovector_contMDiff
    (a : Forms.FormSection Model (U × ComplexPlane₂) ⊤) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model →L[ℝ] ℂ) ∞ (coverCovector a) := by
  intro q
  let x : (⊤ : Opens (U × ComplexPlane₂)) := ⟨q, by trivial⟩
  have hs := Forms.FormSection.inCoordinates_smoothAt Model (U × ComplexPlane₂) a x
  have heq : Forms.inCoordinates Model (U × ComplexPlane₂) a.val q =
      fun y : (⊤ : Opens (U × ComplexPlane₂)) => coverCovector a (y : U × ComplexPlane₂) := by
    funext y
    exact cover_inCoordinates_eq a.val q y
  rw [heq] at hs
  exact contMDiffAt_subtype_iff.mp hs

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
