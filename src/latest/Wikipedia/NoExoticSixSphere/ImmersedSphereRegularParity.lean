import Wikipedia.NoExoticSixSphere.ImmersedSphereFrameParity

/-!
# Frame parity is preserved by an actual smooth family of immersions

The normal columns and spatial derivatives define a genuine homotopy of
injective-operator sphere maps. Its common source twist therefore transports
the original immersed frame obstruction. Immersion is required at every
time of the family, not merely at its endpoints.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (g : ℝ → Sphere 3 → M)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g t) s))

include hg hd in
theorem sphereFrameOperatorMap_homotopic_of_immersed_family
    (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 0))
    (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 0) s))
    (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 1))
    (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 1) s)) :
    (e.sphereFrameOperatorMap a (g 0) hf₀ hd₀).Homotopic
      (e.sphereFrameOperatorMap a (g 1) hf₁ hd₁) := by
  refine ⟨{
    toFun q := ⟨e.normalSpatialOperator a g ((q.1 : ℝ), q.2),
      e.injective_normalSpatialOperator a g hg ((q.1 : ℝ), q.2)
        (hd q.1 q.1.property q.2)⟩
    continuous_toFun := ?_
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl
  }⟩
  exact ((e.contMDiff_normalSpatialOperator a g hg).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

include hg hd in
theorem immersedSphereFrameParity_eq_of_immersed_family
    (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 0))
    (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 0) s))
    (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 1))
    (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 1) s)) :
    e.immersedSphereFrameParity a (g 0) hf₀ hd₀ =
      e.immersedSphereFrameParity a (g 1) hf₁ hd₁ :=
  e.immersedSphereFrameParity_eq_of_frameHomotopic a (g 0) hf₀ hd₀ (g 1) hf₁ hd₁
    (e.sphereFrameOperatorMap_homotopic_of_immersed_family a g hg hd hf₀ hd₀ hf₁ hd₁)

end NoExoticSixSphere.EuclideanEmbedding
