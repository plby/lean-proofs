import Wikipedia.NoExoticSixSphere.SixSphereFramedAttachingProduct
import Wikipedia.NoExoticSixSphere.NormalizedFramedAttachingProduct

/-! # Radius-normalized framed attaching data are constructed for the actual candidate -/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem exists_normalizedFramedAttachingProduct (h : M ≃ₜ Sphere 6) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ A : FramedAttachingProduct e a f, A.radius = 2 ∧
      FramedAttachingProduct.UnroundedTrace.handleRadius A = 1 := by
  obtain ⟨A⟩ := e.nonempty_framedAttachingProduct a h f hf hi hd
  exact ⟨A.normalizedRadius, A.normalizedRadius_radius, A.normalizedRadius_handleRadius⟩

end NoExoticSixSphere.EuclideanEmbedding
