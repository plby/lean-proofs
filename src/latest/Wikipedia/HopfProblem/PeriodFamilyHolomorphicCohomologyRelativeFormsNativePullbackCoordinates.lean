import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Native cotangent pullback in the actual tangent trivializations

The covectors and manifold derivatives below belong to the original
tangent bundles. The coordinate identity is proved by cancelling the
actual target tangent trivialization with its inverse. No constant
trivialization of either manifold's tangent bundle is assumed.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

/-- A map regarded as taking values in the literal full open set. -/
abbrev toTop {M N : Type} [TopologicalSpace N] (f : M → N) (x : M) : (⊤ : Opens N) :=
  ⟨f x, by trivial⟩

@[simp] theorem toTop_coe {M N : Type} [TopologicalSpace N] (f : M → N) (x : M) :
    (toTop f x : N) = f x := rfl

variable (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (M N : Type) [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- Literal pullback of native covectors by the actual real manifold derivative. -/
def realPullback (f : M → N)
    (a : ∀ y : (⊤ : Opens N), Forms.Covector F N (y : N))
    (x : (⊤ : Opens M)) : Forms.Covector E M (x : M) :=
  (a (toTop f (x : M))).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (x : M))

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
/-- The original native covector formula, evaluated on an actual tangent vector. -/
theorem realPullback_apply (f : M → N)
    (a : ∀ y : (⊤ : Opens N), Forms.Covector F N (y : N))
    (x : (⊤ : Opens M)) (v : TangentSpace 𝓘(ℝ, E) (x : M)) :
    realPullback E F M N f a x v =
      a (toTop f (x : M)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (x : M) v) := rfl

/-- In the actual native tangent coordinates, pullback is composition of
the original covector coordinates with the actual derivative coordinates. -/
theorem realPullback_inCoordinates (f : M → N)
    (a : ∀ y : (⊤ : Opens N), Forms.Covector F N (y : N))
    (x₀ : M) (x : (⊤ : Opens M))
    (hx : f (x : M) ∈ (chartAt F (f x₀)).source) :
    Forms.inCoordinates E M (realPullback E F M N f a) x₀ x =
      (Forms.inCoordinates F N a (f x₀) (toTop f (x : M))).comp
        (inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, F) id f
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f) x₀ (x : M)) := by
  have hT : f (x : M) ∈
      (trivializationAt F (TangentSpace 𝓘(ℝ, F)) (f x₀)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  apply ContinuousLinearMap.ext
  intro v
  simp only [Forms.inCoordinates_apply, realPullback, ContinuousLinearMap.comp_apply,
    inTangentCoordinates, ContinuousLinearMap.inCoordinates, Function.id_def]
  rw [Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hT]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
