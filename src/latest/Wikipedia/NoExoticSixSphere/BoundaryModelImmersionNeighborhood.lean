import Wikipedia.NoExoticSixSphere.SmoothImmersionTangentLift
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Open differential regularity in models with boundary

The differential is continuous in actual tangent trivializations. Openness of
injective operators therefore gives an open immersion locus without assuming
that the source model is boundaryless. For equal dimensions this also gives
an open locus of invertible differentials; no local inverse is asserted.
-/

noncomputable section

open Function Filter Bundle Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem eventually_injective_mvfderiv_of_contMDiff {f : M → F} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hi : Injective (mvfderiv I f x)) :
    ∀ᶠ y in 𝓝 x, Injective (mvfderiv I f y) := by
  let τ := trivializationAt E (TangentSpace I) x
  let D : M → E →L[ℝ] F := ImmersionTangentLift.localDifferential I f x
  have hD : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ D x :=
    hf.contMDiffAt.mfderiv_const (by simp)
  have hxτ : x ∈ τ.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hiτ : Injective (τ.symmL ℝ x) := by
    rw [← Trivialization.symm_continuousLinearEquivAt_eq _ hxτ]
    exact ContinuousLinearEquiv.injective _
  have hiD : Injective (D x) := by
    rw [show D x = ImmersionTangentLift.localDifferential I f x x from rfl,
      ImmersionTangentLift.localDifferential_eq]
    exact hi.comp hiτ
  have he : ∀ᶠ y in 𝓝 x, Injective (D y) :=
    hD.continuousAt (ContinuousLinearMap.isOpen_injective.mem_nhds hiD)
  filter_upwards [he, τ.open_baseSet.mem_nhds hxτ] with y hy hyτ
  have hsτ : Surjective (τ.symmL ℝ y) := by
    rw [← Trivialization.symm_continuousLinearEquivAt_eq _ hyτ]
    exact ContinuousLinearEquiv.surjective _
  rw [show D y = ImmersionTangentLift.localDifferential I f x y from rfl,
    ImmersionTangentLift.localDifferential_eq] at hy
  intro v w hvw
  obtain ⟨v', rfl⟩ := hsτ v
  obtain ⟨w', rfl⟩ := hsτ w
  exact congrArg (τ.symmL ℝ y) (hy hvw)

theorem isOpen_injective_mvfderiv {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    IsOpen {x | Injective (mvfderiv I f x)} := by
  rw [isOpen_iff_eventually]
  exact fun _ hx ↦ eventually_injective_mvfderiv_of_contMDiff hf hx

theorem isOpen_bijective_mvfderiv {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    IsOpen {x | Bijective (mvfderiv I f x)} := by
  rw [isOpen_iff_eventually]
  intro x hx
  let L : E →ₗ[ℝ] F := (mvfderiv I f x).toLinearMap
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F :=
    (LinearEquiv.ofBijective L hx).finrank_eq
  filter_upwards [eventually_injective_mvfderiv_of_contMDiff hf hx.1] with y hy
  exact ⟨hy, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hy⟩

end NoExoticSixSphere
