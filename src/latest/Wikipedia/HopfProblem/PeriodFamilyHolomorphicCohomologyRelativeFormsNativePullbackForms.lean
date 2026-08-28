import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsNativePullbackSmooth
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsNativeDerivative
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeGeometrySmooth

/-!
# Genuine pullback of native antiholomorphic form sections

The section below is the actual cotangent pullback by the real manifold
derivative. Smoothness is verified in the original Hom-bundle charts;
anti-linearity follows from complex differentiability in the unchanged
source and target atlases.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

variable (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  (M N : Type) [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- Pullback of an actual native antiholomorphic form by a genuinely
holomorphic map, preserving the original cotangent bundles. -/
def formPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f)
    (a : Forms.FormSection F N ⊤) : Forms.FormSection E M ⊤ :=
  Forms.sectionMk E M ⊤ (realPullback E F M N f a.val)
    (realPullback_smooth E F M N f (Geometry.contMDiff_real_of_complex M hf)
      a.val (Forms.FormSection.smooth F N a)) (by
        intro x
        exact pullback_mem_antiCovectors
          ((hf (x : M)).mdifferentiableAt (show ∞ ≠ (0 : ℕ∞ω) by simp))
          ⟨Forms.covectorAsModel F N (a (toTop f (x : M))),
            Forms.FormSection.anti F N a (toTop f (x : M))⟩)

/-- The constructed native form is literally composition with the
original real manifold derivative, on each actual tangent vector. -/
theorem formPullback_apply (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f)
    (a : Forms.FormSection F N ⊤) (x : (⊤ : Opens M))
    (v : TangentSpace 𝓘(ℝ, E) (x : M)) :
    formPullback E F M N f hf a x v =
      a (toTop f (x : M)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (x : M) v) := rfl

/-- Native tangent-space aliases give the same literal model-vector
formula, with no tangent-bundle triviality assumption. -/
theorem formPullback_model_apply (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f)
    (a : Forms.FormSection F N ⊤) (x : (⊤ : Opens M)) (v : E) :
    Forms.covectorAsModel E M (formPullback E F M N f hf a x) v =
      Forms.covectorAsModel F N (a (toTop f (x : M)))
        ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (x : M)) v) := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
