import Wikipedia.NoExoticSixSphere.SmoothInjectiveOperatorLift
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth tangent-bundle lifts through an actual immersion

Smoothness is proved in genuine tangent trivializations. The unadjusted
coordinate formula for the manifold differential is not assumed smooth.
The source model may have boundary and need not have an inner-product norm.
-/

noncomputable section

open Function Filter Bundle
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.ImmersionTangentLift

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def localDifferential (f : M → F) (x₀ : M) : M → E →L[ℝ] F :=
  inTangentCoordinates I 𝓘(ℝ, F) id f (mfderiv I 𝓘(ℝ, F) f) x₀

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem localDifferential_eq (f : M → F) (x₀ y : M) :
    localDifferential I f x₀ y = (mvfderiv I f y).comp
      ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y) := by
  simp only [localDifferential, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  rfl

variable {B K X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace K] {J : ModelWithCorners ℝ B K}
  [TopologicalSpace X] [ChartedSpace K X]

theorem contMDiff_lift {f : M → F} {g : X → M} {v : X → F}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hg : ContMDiff J I ∞ g)
    (hv : ContMDiff J 𝓘(ℝ, F) ∞ v) (hi : ∀ m, Injective (mvfderiv I f m))
    (w : ∀ x, TangentSpace I (g x)) (hw : ∀ x, mvfderiv I f (g x) (w x) = v x) :
    ContMDiff J (I.prod 𝓘(ℝ, E)) ∞
      (fun x ↦ (TotalSpace.mk' E (g x) (w x) : TangentBundle I M)) := by
  intro x
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hg x, ?_⟩
  let τ := trivializationAt E (TangentSpace I) (g x)
  let A : X → E →L[ℝ] F := fun y ↦ localDifferential I f (g x) (g y)
  let c : X → E := fun y ↦ (τ (TotalSpace.mk' E (g y) (w y))).2
  change ContMDiffAt J 𝓘(ℝ, E) ∞ c x
  have hA : ContMDiffAt J 𝓘(ℝ, E →L[ℝ] F) ∞ A x :=
    (hf.contMDiffAt.mfderiv_const (by simp)).comp x (hg x)
  have hτ : g x ∈ τ.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (g x)
  have hiτ : Injective (τ.symmL ℝ (g x)) := by
    rw [← Trivialization.symm_continuousLinearEquivAt_eq _ hτ]
    exact ContinuousLinearEquiv.injective _
  have hiA : Injective (A x) := by
    rw [show A x = localDifferential I f (g x) (g x) from rfl, localDifferential_eq]
    exact (hi (g x)).comp hiτ
  apply contMDiffAt_of_eventually_injective_apply_eq hA (hv x) hiA
  filter_upwards [(hg x).continuousAt (τ.open_baseSet.mem_nhds hτ)] with y hy
  change localDifferential I f (g x) (g y) (c y) = v y
  rw [localDifferential_eq]
  change mvfderiv I f (g y) (τ.symmL ℝ (g y) (c y)) = v y
  have hc := τ.symmL_continuousLinearMapAt (R := ℝ) hy (w y)
  rw [τ.continuousLinearMapAt_apply_of_mem ℝ hy (w y)] at hc
  rw [show τ.symmL ℝ (g y) (c y) = w y from hc]
  exact hw y

end NoExoticSixSphere.ImmersionTangentLift
