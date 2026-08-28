import Wikipedia.NoExoticSixSphere.SelfTransverseSphereRepresentative

/-!
# Immersed representatives of arbitrary continuous three-sphere maps

Apply the actual generic-family construction to a constant smooth family.
Its interior singularities form a discrete subset of a second-countable
space, hence occur at only countably many times. An interior time outside
that set gives a smooth immersion. Restricting the family from its original
zero endpoint to that time supplies the required ordinary homotopy.
This construction does not remove double points or assert an embedding.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization ManifoldAffineSphereFamily SphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_immersed_homotopic_of_smooth (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s) := by
  obtain ⟨g, hg, H, hd, _⟩ := e.exists_selfTransverse_immersed_homotopic_of_smooth r f hf
  exact ⟨g, hg, H, hd⟩

include e r in
theorem exists_immersed_homotopic (f : C(Sphere 3, M)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s) := by
  obtain ⟨F, hF, HF⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 3) (J := 𝓡 6) f
  obtain ⟨g, hg, H, hd⟩ := e.exists_immersed_homotopic_of_smooth r F hF
  exact ⟨g, hg, HF.trans H, hd⟩

end NoExoticSixSphere.EuclideanEmbedding
